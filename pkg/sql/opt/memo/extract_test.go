// Copyright 2026 The Cockroach Authors.
//
// Use of this software is governed by the CockroachDB Software License
// included in the /LICENSE file.

package memo

import (
	"context"
	"testing"

	"github.com/cockroachdb/cockroach/pkg/settings/cluster"
	"github.com/cockroachdb/cockroach/pkg/sql/opt"
	"github.com/cockroachdb/cockroach/pkg/sql/sem/eval"
	"github.com/cockroachdb/cockroach/pkg/sql/sem/tree"
	"github.com/cockroachdb/cockroach/pkg/sql/types"
	"github.com/stretchr/testify/require"
)

// TestExtractTailCalls tests the ExtractTailCalls function with various
// expression types. It uses the Memo's Memoize methods to construct
// expressions. Each test case contains a single tail-call candidate.
func TestExtractTailCalls(t *testing.T) {
	// Set up a Memo instance for constructing expressions.
	var mem Memo
	evalCtx := eval.MakeTestingEvalContext(cluster.MakeTestingClusterSettings())
	mem.Init(context.Background(), &evalCtx)

	// The tail-call candidate that we'll use throughout tests.
	// Create a VALUES with a single row and single column.
	col := mem.Metadata().AddColumn("subquery_col", types.Int)
	tailCallCandidate := mem.MemoizeSubquery(
		mem.MemoizeValues(
			ScalarListExpr{
				mem.MemoizeTuple(
					ScalarListExpr{mem.MemoizeConst(tree.NewDInt(1), types.Int)},
					types.MakeTuple([]*types.T{types.Int}),
				),
			},
			&ValuesPrivate{
				Cols: opt.ColList{col},
			},
		),
		&SubqueryPrivate{},
	)

	// Helper to build a VALUES expression with specific number of rows.
	makeValues := func(numRows int) RelExpr {
		rows := make(ScalarListExpr, numRows)
		for i := range rows {
			rows[i] = mem.MemoizeTuple(ScalarListExpr{mem.MemoizeTrue()}, types.MakeTuple([]*types.T{types.Bool}))
		}
		return mem.MemoizeValues(rows, &ValuesPrivate{
			Cols: opt.ColList{mem.Metadata().AddColumn("col", types.Bool)},
		})
	}

	// Helper to build ProjectionsItem from a scalar expression.
	makeProjectionsItem := func(element opt.ScalarExpr) ProjectionsItem {
		col := mem.Metadata().AddColumn("proj", types.Int)
		item := ProjectionsItem{
			Element: element,
			Col:     col,
		}
		item.PopulateProps(&mem)
		return item
	}

	// Helper to build a ProjectExpr with specific cardinality.
	// To control cardinality, we use an input with the desired number of rows.
	makeProject := func(numInputRows int, projections ProjectionsExpr, passthrough opt.ColSet) RelExpr {
		input := makeValues(numInputRows)
		return mem.MemoizeProject(input, projections, passthrough)
	}

	testCases := []struct {
		name       string
		expr       opt.Expr
		isTailCall bool // Whether the candidate should be identified as a tail call
	}{
		// ProjectExpr cases
		{
			name: "ProjectExpr with valid tail call",
			expr: makeProject(
				1, // Single row => cardinality 0-1
				ProjectionsExpr{makeProjectionsItem(tailCallCandidate)},
				opt.ColSet{},
			),
			isTailCall: true,
		},
		{
			name: "ProjectExpr with cardinality > 1",
			expr: makeProject(
				2, // Two rows => cardinality > 1
				ProjectionsExpr{makeProjectionsItem(tailCallCandidate)},
				opt.ColSet{},
			),
			isTailCall: false,
		},
		{
			name: "ProjectExpr with multiple projections",
			expr: makeProject(
				1,
				ProjectionsExpr{
					makeProjectionsItem(mem.MemoizeConst(tree.NewDInt(1), types.Int)),
					makeProjectionsItem(tailCallCandidate),
				},
				opt.ColSet{},
			),
			isTailCall: false,
		},
		{
			name: "ProjectExpr with non-empty passthrough",
			expr: func() RelExpr {
				// Create a VALUES input that includes the passthrough column.
				passthroughCol := mem.Metadata().AddColumn("passthrough", types.Int)
				input := mem.MemoizeValues(
					ScalarListExpr{
						mem.MemoizeTuple(
							ScalarListExpr{mem.MemoizeConst(tree.NewDInt(1), types.Int)},
							types.MakeTuple([]*types.T{types.Int}),
						),
					},
					&ValuesPrivate{
						Cols: opt.ColList{passthroughCol},
					},
				)
				passthrough := opt.ColSet{}
				passthrough.Add(passthroughCol)
				return mem.MemoizeProject(input, ProjectionsExpr{makeProjectionsItem(tailCallCandidate)}, passthrough)
			}(),
			isTailCall: false,
		},

		// ValuesExpr cases
		{
			name: "ValuesExpr with single row, single element",
			expr: mem.MemoizeValues(
				ScalarListExpr{
					mem.MemoizeTuple(ScalarListExpr{tailCallCandidate}, types.MakeTuple([]*types.T{types.Int})),
				},
				&ValuesPrivate{
					Cols: opt.ColList{mem.Metadata().AddColumn("col", types.Int)},
				},
			),
			isTailCall: true,
		},
		{
			name: "ValuesExpr with multiple rows",
			expr: mem.MemoizeValues(
				ScalarListExpr{
					mem.MemoizeTuple(ScalarListExpr{tailCallCandidate}, types.MakeTuple([]*types.T{types.Int})),
					mem.MemoizeTuple(ScalarListExpr{mem.MemoizeConst(tree.NewDInt(1), types.Int)}, types.MakeTuple([]*types.T{types.Int})),
				},
				&ValuesPrivate{
					Cols: opt.ColList{mem.Metadata().AddColumn("col", types.Int)},
				},
			),
			isTailCall: false,
		},
		{
			name: "ValuesExpr with multiple elements",
			expr: mem.MemoizeValues(
				ScalarListExpr{
					mem.MemoizeTuple(
						ScalarListExpr{
							tailCallCandidate,
							mem.MemoizeConst(tree.NewDInt(1), types.Int),
						},
						types.MakeTuple([]*types.T{types.Int, types.Int}),
					),
				},
				&ValuesPrivate{
					Cols: opt.ColList{
						mem.Metadata().AddColumn("col1", types.Int),
						mem.Metadata().AddColumn("col2", types.Int),
					},
				},
			),
			isTailCall: false,
		},

		// CaseExpr cases
		{
			name: "CaseExpr with tail call in WHEN branch",
			expr: mem.MemoizeCase(
				TrueSingleton,
				ScalarListExpr{
					mem.MemoizeWhen(TrueSingleton, tailCallCandidate),
				},
				mem.MemoizeConst(tree.NewDInt(1), types.Int),
			),
			isTailCall: true,
		},
		{
			name: "CaseExpr with tail call in ELSE branch",
			expr: mem.MemoizeCase(
				TrueSingleton,
				ScalarListExpr{
					mem.MemoizeWhen(TrueSingleton, mem.MemoizeConst(tree.NewDInt(1), types.Int)),
				},
				tailCallCandidate,
			),
			isTailCall: true,
		},

		// SubqueryExpr case
		{
			name:       "SubqueryExpr is a tail call",
			expr:       tailCallCandidate,
			isTailCall: true,
		},

		// UDFCallExpr cases
		{
			name: "UDFCallExpr (not set-returning) is a tail call",
			expr: mem.MemoizeUDFCall(
				ScalarListExpr{},
				&UDFCallPrivate{
					Def: &UDFDefinition{
						SetReturning: false,
					},
				},
			),
			isTailCall: true,
		},
		{
			name: "UDFCallExpr (set-returning) is not a tail call",
			expr: mem.MemoizeUDFCall(
				ScalarListExpr{},
				&UDFCallPrivate{
					Def: &UDFDefinition{
						SetReturning: true,
					},
				},
			),
			isTailCall: false,
		},

		// DistributeExpr cases
		{
			name: "DistributeExpr recursively processes input",
			expr: &DistributeExpr{
				Input: mem.MemoizeValues(
					ScalarListExpr{
						mem.MemoizeTuple(ScalarListExpr{tailCallCandidate}, types.MakeTuple([]*types.T{types.Int})),
					},
					&ValuesPrivate{
						Cols: opt.ColList{mem.Metadata().AddColumn("col", types.Int)},
					},
				),
			},
			isTailCall: true,
		},
		{
			name: "DistributeExpr with nested ProjectExpr",
			expr: &DistributeExpr{
				Input: makeProject(
					1,
					ProjectionsExpr{makeProjectionsItem(tailCallCandidate)},
					opt.ColSet{},
				),
			},
			isTailCall: true,
		},

		// Non-tail-call expression
		{
			name:       "ConstExpr is not a tail call",
			expr:       mem.MemoizeConst(tree.NewDInt(1), types.Int),
			isTailCall: false,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			tailCalls := make(map[opt.ScalarExpr]struct{})
			ExtractTailCalls(tc.expr, tailCalls)
			if tc.isTailCall {
				require.NotEmpty(t, tailCalls, "expected at least one tail call")
			} else {
				require.Empty(t, tailCalls, "expected no tail calls")
			}
		})
	}
}
