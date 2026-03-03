// Copyright 2018 The Cockroach Authors.
//
// Use of this software is governed by the CockroachDB Software License
// included in the /LICENSE file.

package norm

import (
	"github.com/cockroachdb/cockroach/pkg/sql/opt"
	"github.com/cockroachdb/cockroach/pkg/sql/opt/memo"
	"github.com/cockroachdb/cockroach/pkg/sql/opt/props"
	"github.com/cockroachdb/cockroach/pkg/util/intsets"
	"github.com/cockroachdb/errors"
)

// RejectNullCols returns the set of columns that are candidates for NULL
// rejection filter pushdown. See the Relational.Rule.RejectNullCols comment for
// more details.
func (c *CustomFuncs) RejectNullCols(in memo.RelExpr) opt.ColSet {
	return DeriveRejectNullCols(c.mem, in, c.f.disabledRules)
}

// HasNullRejectingFilter returns true if the filter causes some of the columns
// in nullRejectCols to be non-null. For example, if nullRejectCols = (x, z),
// filters such as x < 5, x = y, and z IS NOT NULL all satisfy this property.
func (c *CustomFuncs) HasNullRejectingFilter(
	filters memo.FiltersExpr, nullRejectCols opt.ColSet,
) bool {
	if nullRejectCols.Empty() {
		return false
	}
	for i := range filters {
		constraints := filters[i].ScalarProps().Constraints
		if constraints == nil {
			continue
		}

		var notNullFilterCols opt.ColSet
		constraints.ExtractNotNullCols(c.f.ctx, c.f.evalCtx, &notNullFilterCols)
		if notNullFilterCols.Intersects(nullRejectCols) {
			return true
		}
	}
	return false
}

// NullRejectAggVar scans through the list of aggregate functions and returns
// the Variable input of the first aggregate that is not ConstAgg. Such an
// aggregate must exist, since this is only called if at least one eligible
// null-rejection column was identified by the deriveGroupByRejectNullCols
// method (see its comment for more details).
func (c *CustomFuncs) NullRejectAggVar(
	aggs memo.AggregationsExpr, nullRejectCols opt.ColSet,
) *memo.VariableExpr {
	for i := range aggs {
		if nullRejectCols.Contains(aggs[i].Col) {
			return memo.ExtractAggFirstVar(aggs[i].Agg)
		}
	}
	panic(errors.AssertionFailedf("expected aggregation not found"))
}

// NullRejectProjections returns a Variable for the first eligible input column
// of the first projection that is referenced by nullRejectCols. A column is
// only null-rejected if:
//
//  1. It is in the RejectNullCols ColSet of the input expression (null
//     rejection has been requested)
//
//  2. A NULL in the column implies that the projection will also be NULL.
//
// NullRejectProjections panics if no such projection is found.
func (c *CustomFuncs) NullRejectProjections(
	projections memo.ProjectionsExpr, nullRejectCols, inputNullRejectCols opt.ColSet,
) opt.ScalarExpr {

	// getFirstEligibleCol recursively traverses the given expression and returns
	// the first column that is eligible for null-rejection. Returns 0 if no such
	// column is found.
	var getFirstEligibleCol func(opt.Expr) opt.ColumnID
	getFirstEligibleCol = func(expr opt.Expr) opt.ColumnID {
		switch t := expr.(type) {
		case *memo.VariableExpr:
			if inputNullRejectCols.Contains(t.Col) {
				// Null-rejection has been requested for this column, and the projection
				// returns NULL when this column is NULL.
				return t.Col
			}
		case *memo.CaseExpr:
			// Match the specific pattern of CASE WHEN
			whenExpr := t.Whens[0].(*memo.WhenExpr)
			if t.Input.Op() == opt.TrueOp {
				if isExpr, ok := whenExpr.Condition.(*memo.IsExpr); ok {
					leftVar, leftIsVar := isExpr.Left.(*memo.VariableExpr)
					_, rightIsNull := isExpr.Right.(*memo.NullExpr)
					_, resIsNull := whenExpr.Value.(*memo.NullExpr)
					if leftIsVar && inputNullRejectCols.Contains(leftVar.Col) && rightIsNull && resIsNull {
						return leftVar.Col
					}
				}
			}
		default:
			if opt.ScalarOperatorTransmitsNulls(expr.Op()) {
				// This operator return NULLs when one of its inputs is NULL.
				for i, cnt := 0, expr.ChildCount(); i < cnt; i++ {
					if col := getFirstEligibleCol(expr.Child(i)); col != 0 {
						return col
					}
				}
			}
		}
		return opt.ColumnID(0)
	}

	for i := range projections {
		if nullRejectCols.Contains(projections[i].Col) {
			col := getFirstEligibleCol(projections[i].Element)
			if col == 0 {
				// If the ColumnID of the projection was in nullRejectCols, an input
				// column must exist that can be null-rejected.
				panic(errors.AssertionFailedf("expected column not found"))
			}
			return c.f.ConstructVariable(col)
		}
	}
	panic(errors.AssertionFailedf("expected projection not found"))
}

// DeriveRejectNullCols returns the set of columns that are candidates for NULL
// rejection filter pushdown. See the Relational.Rule.RejectNullCols comment for
// more details.
//
// disabledRules is the set of rules currently disabled, only used when rules
// are randomly disabled for testing. It is used to prevent propagating the
// RejectNullCols property when the corresponding column-pruning normalization
// rule is disabled. This prevents rule cycles during testing.
func DeriveRejectNullCols(mem *memo.Memo, in memo.RelExpr, disabledRules intsets.Fast) opt.ColSet {
	// Lazily calculate and store the RejectNullCols value.
	relProps := in.Relational()
	if relProps.IsAvailable(props.RejectNullCols) {
		return relProps.Rule.RejectNullCols
	}
	relProps.SetAvailable(props.RejectNullCols)

	// TODO(andyk): Add other operators to make null rejection more comprehensive.
	switch in.Op() {
	case opt.InnerJoinOp, opt.InnerJoinApplyOp:
		if disabledRules.Contains(int(opt.MergeSelectInnerJoin)) ||
			disabledRules.Contains(int(opt.PushFilterIntoJoinLeft)) ||
			disabledRules.Contains(int(opt.PushFilterIntoJoinRight)) ||
			disabledRules.Contains(int(opt.MapFilterIntoJoinLeft)) ||
			disabledRules.Contains(int(opt.MapFilterIntoJoinRight)) {
			// Avoid rule cycles.
			break
		}
		// Pass through null-rejecting columns from both inputs.
		if in.Child(0).(memo.RelExpr).Relational().OuterCols.Empty() {
			relProps.Rule.RejectNullCols.UnionWith(
				DeriveRejectNullCols(mem, in.Child(0).(memo.RelExpr), disabledRules),
			)
		}
		if in.Child(1).(memo.RelExpr).Relational().OuterCols.Empty() {
			relProps.Rule.RejectNullCols.UnionWith(
				DeriveRejectNullCols(mem, in.Child(1).(memo.RelExpr), disabledRules),
			)
		}

	case opt.LeftJoinOp, opt.LeftJoinApplyOp:
		if disabledRules.Contains(int(opt.RejectNullsLeftJoin)) ||
			disabledRules.Contains(int(opt.PushSelectCondLeftIntoJoinLeftAndRight)) {
			// Avoid rule cycles.
			break
		}
		// Pass through null-rejection columns from left input, and request
		// null-rejection on right columns.
		if in.Child(0).(memo.RelExpr).Relational().OuterCols.Empty() {
			relProps.Rule.RejectNullCols.UnionWith(
				DeriveRejectNullCols(mem, in.Child(0).(memo.RelExpr), disabledRules),
			)
		}
		relProps.Rule.RejectNullCols.UnionWith(in.Child(1).(memo.RelExpr).Relational().OutputCols)

	case opt.RightJoinOp:
		if disabledRules.Contains(int(opt.RejectNullsRightJoin)) ||
			disabledRules.Contains(int(opt.CommuteRightJoin)) {
			// Avoid rule cycles.
			break
		}
		// Pass through null-rejection columns from right input, and request
		// null-rejection on left columns.
		relProps.Rule.RejectNullCols.UnionWith(in.Child(0).(memo.RelExpr).Relational().OutputCols)
		if in.Child(1).(memo.RelExpr).Relational().OuterCols.Empty() {
			relProps.Rule.RejectNullCols.UnionWith(
				DeriveRejectNullCols(mem, in.Child(1).(memo.RelExpr), disabledRules),
			)
		}

	case opt.FullJoinOp:
		if disabledRules.Contains(int(opt.RejectNullsLeftJoin)) ||
			disabledRules.Contains(int(opt.RejectNullsRightJoin)) {
			// Avoid rule cycles.
			break
		}
		// Request null-rejection on all output columns.
		relProps.Rule.RejectNullCols.UnionWith(relProps.OutputCols)

	case opt.GroupByOp, opt.ScalarGroupByOp:
		if disabledRules.Contains(int(opt.RejectNullsGroupBy)) ||
			disabledRules.Contains(int(opt.PushSelectIntoGroupBy)) {
			// Avoid rule cycles.
			break
		}
		relProps.Rule.RejectNullCols.UnionWith(deriveGroupByRejectNullCols(mem, in, disabledRules))

	case opt.ProjectOp:
		if disabledRules.Contains(int(opt.RejectNullsProject)) ||
			disabledRules.Contains(int(opt.PushSelectIntoProject)) {
			// Avoid rule cycles.
			break
		}
		relProps.Rule.RejectNullCols.UnionWith(deriveProjectRejectNullCols(mem, in, disabledRules))

	case opt.ScanOp:
		relProps.Rule.RejectNullCols.UnionWith(deriveScanRejectNullCols(mem, in))
	}

	// Don't attempt to request null-rejection for non-null cols. This can happen
	// if normalization failed to null-reject, and then exploration "uncovered"
	// the possibility for null-rejection of a column.
	relProps.Rule.RejectNullCols.DifferenceWith(relProps.NotNullCols)

	return relProps.Rule.RejectNullCols
}

// deriveGroupByRejectNullCols returns the set of GroupBy columns that are
// eligible for null rejection. If an aggregate input column has requested null
// rejection, then pass along its request if the following criteria are met:
//
//  1. The aggregate function ignores null values, meaning that its value
//     would not change if input null values are filtered.
//
//  2. The aggregate function returns null if its input is empty. And since
//     by #1, the presence of nulls does not alter the result, the aggregate
//     function would return null if its input contains only null values.
func deriveGroupByRejectNullCols(
	mem *memo.Memo, in memo.RelExpr, disabledRules intsets.Fast,
) opt.ColSet {
	input := in.Child(0).(memo.RelExpr)
	aggs := *in.Child(1).(*memo.AggregationsExpr)

	var rejectNullCols opt.ColSet
	var savedInColID opt.ColumnID
	for i := range aggs {
		agg := memo.ExtractAggFunc(aggs[i].Agg)
		aggOp := agg.Op()

		if aggOp == opt.ConstAggOp {
			continue
		}

		// Criteria #1 and #2.
		if !opt.AggregateIgnoresNulls(aggOp) || !opt.AggregateIsNullOnEmpty(aggOp) {
			// Can't reject nulls for the aggregate.
			return opt.ColSet{}
		}

		// Get column ID of aggregate's Variable operator input.
		inColID := agg.Child(0).(*memo.VariableExpr).Col

		// Criteria #3.
		if savedInColID != 0 && savedInColID != inColID {
			// Multiple columns used by aggregate functions, so can't reject nulls
			// for any of them.
			return opt.ColSet{}
		}
		savedInColID = inColID

		if !DeriveRejectNullCols(mem, input, disabledRules).Contains(inColID) {
			// Input has not requested null rejection on the input column.
			return opt.ColSet{}
		}

		// Can possibly reject column, but keep searching, since if
		// multiple columns are used by aggregate functions, then nulls
		// can't be rejected on any column.
		rejectNullCols.Add(aggs[i].Col)
	}
	return rejectNullCols
}

// GetNullRejectedCols returns the set of columns which are null-rejected by the
// given FiltersExpr.
func (c *CustomFuncs) GetNullRejectedCols(filters memo.FiltersExpr) opt.ColSet {
	var nullRejectedCols opt.ColSet
	for i := range filters {
		constraints := filters[i].ScalarProps().Constraints
		if constraints == nil {
			continue
		}

		constraints.ExtractNotNullCols(c.f.ctx, c.f.evalCtx, &nullRejectedCols)
	}
	return nullRejectedCols
}

// MakeNullRejectFilters returns a FiltersExpr with a "col IS NOT NULL" conjunct
// for each column in the given ColSet.
func (c *CustomFuncs) MakeNullRejectFilters(nullRejectCols opt.ColSet) memo.FiltersExpr {
	filters := make(memo.FiltersExpr, 0, nullRejectCols.Len())
	for col, ok := nullRejectCols.Next(0); ok; col, ok = nullRejectCols.Next(col + 1) {
		filters = append(
			filters,
			c.f.ConstructFiltersItem(c.f.ConstructIsNot(c.f.ConstructVariable(col), memo.NullSingleton)),
		)
	}
	return filters
}

// deriveProjectRejectNullCols returns the set of Project output columns which
// are eligible for null rejection. All passthrough columns which are in the
// RejectNullCols set of the input can be null-rejected. In addition, projected
// columns can also be null-rejected when:
//
//  1. The projection "transmits" nulls - it returns NULL when one or more of
//     its inputs is NULL.
func deriveProjectRejectNullCols(
	mem *memo.Memo, in memo.RelExpr, disabledRules intsets.Fast,
) opt.ColSet {
	rejectNullCols := DeriveRejectNullCols(mem, in.Child(0).(memo.RelExpr), disabledRules)
	projections := *in.Child(1).(*memo.ProjectionsExpr)

	// Add any projections which satisfy the conditions.
	var projectionsRejectCols opt.ColSet
	for i := range projections {
		if exprTransmitsNulls(projections[i].Element, rejectNullCols) {
			projectionsRejectCols.Add(projections[i].Col)
		}
	}
	return (rejectNullCols.Union(projectionsRejectCols)).Intersection(in.Relational().OutputCols)
}

// ExprTransmitsNulls wraps the exprTransmitsNulls function for use in optgen.
func (c *CustomFuncs) ExprTransmitsNulls(expr opt.Expr, cols opt.ColSet) bool {
	return exprTransmitsNulls(expr, cols)
}

// exprTransmitsNulls returns true if the given expression "transmits" NULLs
// from the given columns. In other words, it returns true if a NULL value in
// at least one of the given columns implies that the expression will also be
// NULL. This is used to determine whether a projection can be null-rejected.
func exprTransmitsNulls(expr opt.Expr, cols opt.ColSet) bool {
	switch t := expr.(type) {
	case *memo.VariableExpr:
		// If the column contained by this Variable is in the input column set, the
		// expression transmits NULLs.
		return cols.Contains(t.Col)

	case *memo.CaseExpr:
		// Handle the common case when the CASE expression directly returns NULL if
		// the input column is NULL. This situation is produced by various optimizer
		// rules.
		whenExpr := t.Whens[0].(*memo.WhenExpr)
		if t.Input.Op() == opt.TrueOp {
			if isExpr, ok := whenExpr.Condition.(*memo.IsExpr); ok {
				leftVar, leftIsVar := isExpr.Left.(*memo.VariableExpr)
				_, rightIsNull := isExpr.Right.(*memo.NullExpr)
				_, resIsNull := whenExpr.Value.(*memo.NullExpr)
				if leftIsVar && cols.Contains(leftVar.Col) && rightIsNull && resIsNull {
					return true
				}
			}
		}

	default:
		if opt.ScalarOperatorTransmitsNulls(expr.Op()) {
			// In order for an expression to transmit NULLs, we require an unbroken
			// chain of null-transmitting operators from the input null-rejection
			// column to the root of the expression.
			for i, cnt := 0, expr.ChildCount(); i < cnt; i++ {
				if exprTransmitsNulls(expr.Child(i), cols) {
					return true
				}
			}
		}
	}
	return false
}

// deriveScanRejectNullCols returns the set of Scan columns which are eligible
// for null rejection. Scan columns can be null-rejected only when there are
// partial indexes that have explicit "column IS NOT NULL" expressions. Creating
// null-rejecting filters is useful in this case because the filters may imply a
// partial index predicate expression, allowing a scan over the index.
func deriveScanRejectNullCols(mem *memo.Memo, in memo.RelExpr) opt.ColSet {
	md := mem.Metadata()
	scan := in.(*memo.ScanExpr)

	var rejectNullCols opt.ColSet
	for i, n := 0, md.Table(scan.Table).IndexCount(); i < n; i++ {
		if pred, isPartialIndex := md.TableMeta(scan.Table).PartialIndexPredicate(i); isPartialIndex {
			predFilters := *pred.(*memo.FiltersExpr)
			rejectNullCols.UnionWith(isNotNullCols(predFilters))
		}
	}

	// Some of the columns may already be not-null (e.g. if the scan is
	// constrained). Requesting rejection on such columns can lead to infinite
	// rule application (see #64661).
	rejectNullCols.DifferenceWith(in.Relational().NotNullCols)

	return rejectNullCols
}

// isNotNullCols returns the set of columns with explicit, top-level IS NOT NULL
// filter conditions in the given filters. Note that And and Or expressions are
// not traversed.
func isNotNullCols(filters memo.FiltersExpr) opt.ColSet {
	var notNullCols opt.ColSet
	for i := range filters {
		c := filters[i].Condition
		isNot, ok := c.(*memo.IsNotExpr)
		if !ok {
			continue
		}
		col, ok := isNot.Left.(*memo.VariableExpr)
		if !ok {
			continue
		}
		if isNot.Right == memo.NullSingleton {
			notNullCols.Add(col.Col)
		}
	}
	return notNullCols
}
