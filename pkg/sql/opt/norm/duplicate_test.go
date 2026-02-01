// Copyright 2026 The Cockroach Authors.
//
// Use of this software is governed by the CockroachDB Software License
// included in the /LICENSE file.

package norm_test

import (
	"context"
	"testing"

	"github.com/cockroachdb/cockroach/pkg/settings/cluster"
	"github.com/cockroachdb/cockroach/pkg/sql/opt"
	"github.com/cockroachdb/cockroach/pkg/sql/opt/memo"
	"github.com/cockroachdb/cockroach/pkg/sql/opt/norm"
	"github.com/cockroachdb/cockroach/pkg/sql/opt/testutils/testcat"
	"github.com/cockroachdb/cockroach/pkg/sql/sem/eval"
	"github.com/cockroachdb/cockroach/pkg/sql/sem/tree"
	"github.com/cockroachdb/cockroach/pkg/sql/types"
	"github.com/stretchr/testify/require"
)

// TestDuplicateSubtreeAllocatesFreshColumnIDs verifies that column IDs in
// duplicated expressions are fresh and different from the original.
func TestDuplicateSubtreeAllocatesFreshColumnIDs(t *testing.T) {
	evalCtx := eval.MakeTestingEvalContext(cluster.MakeTestingClusterSettings())
	var f norm.Factory
	f.Init(context.Background(), &evalCtx, nil /* catalog */)

	// Create a Values expression with a synthesized column.
	colID := f.Metadata().AddColumn("a", types.Int)
	cols := opt.ColList{colID}
	tupType := types.MakeTuple([]*types.T{types.Int})

	// Create a single row.
	constExpr := f.ConstructConst(tree.NewDInt(1), types.Int)
	tuple := f.ConstructTuple(memo.ScalarListExpr{constExpr}, tupType)
	rows := memo.ScalarListExpr{tuple}

	valuesExpr := f.ConstructValues(rows, &memo.ValuesPrivate{
		Cols: cols,
		ID:   f.Metadata().NextUniqueID(),
	})

	// Duplicate the expression.
	duplicated := f.DuplicateSubtree(valuesExpr)

	// Verify the duplicated expression has different column ID.
	origValues := valuesExpr.(*memo.ValuesExpr)
	dupValues := duplicated.(*memo.ValuesExpr)
	require.NotEqual(t, origValues.Cols[0], dupValues.Cols[0], "duplicated column ID should be different")

	// Verify both column IDs exist in metadata.
	require.NotPanics(t, func() {
		f.Metadata().ColumnMeta(origValues.Cols[0])
		f.Metadata().ColumnMeta(dupValues.Cols[0])
	})
}

// TestDuplicateSubtreeAllocatesFreshTableIDs verifies that table IDs in
// duplicated expressions are fresh and different from the original.
func TestDuplicateSubtreeAllocatesFreshTableIDs(t *testing.T) {
	evalCtx := eval.MakeTestingEvalContext(cluster.MakeTestingClusterSettings())
	catalog := testcat.New()
	_, err := catalog.ExecuteDDL("CREATE TABLE t (a INT PRIMARY KEY, b INT)")
	require.NoError(t, err)

	var f norm.Factory
	f.Init(context.Background(), &evalCtx, catalog)

	// Create a scan expression.
	tn := tree.NewUnqualifiedTableName("t")
	tab := catalog.Table(tn)
	tabID := f.Metadata().AddTable(tab, tn)

	scanPrivate := &memo.ScanPrivate{Table: tabID}
	for i, n := 0, tab.ColumnCount(); i < n; i++ {
		colID := tabID.ColumnID(i)
		scanPrivate.Cols.Add(colID)
	}
	scanExpr := f.ConstructScan(scanPrivate)

	// Duplicate the expression.
	duplicated := f.DuplicateSubtree(scanExpr)

	// Verify the duplicated expression has a different table ID.
	origScan := scanExpr.(*memo.ScanExpr)
	dupScan := duplicated.(*memo.ScanExpr)
	require.NotEqual(t, origScan.Table, dupScan.Table, "duplicated table ID should be different")

	// Verify both table IDs exist in metadata.
	require.NotPanics(t, func() {
		f.Metadata().TableMeta(origScan.Table)
		f.Metadata().TableMeta(dupScan.Table)
	})
}

// TestDuplicateSubtreeConsistentMapping verifies that the same source ID
// always maps to the same destination ID within a single duplication operation.
func TestDuplicateSubtreeConsistentMapping(t *testing.T) {
	evalCtx := eval.MakeTestingEvalContext(cluster.MakeTestingClusterSettings())
	var f norm.Factory
	f.Init(context.Background(), &evalCtx, nil /* catalog */)

	// Create a Values expression where the same column appears twice in projections.
	colID := f.Metadata().AddColumn("a", types.Int)
	cols := opt.ColList{colID, colID} // Same column appears twice
	tupType := types.MakeTuple([]*types.T{types.Int, types.Int})

	// Create a row with two references to the same value.
	constExpr := f.ConstructConst(tree.NewDInt(1), types.Int)
	tuple := f.ConstructTuple(memo.ScalarListExpr{constExpr, constExpr}, tupType)
	rows := memo.ScalarListExpr{tuple}

	valuesExpr := f.ConstructValues(rows, &memo.ValuesPrivate{
		Cols: cols,
		ID:   f.Metadata().NextUniqueID(),
	})

	// Duplicate the Values expression.
	duplicated := f.DuplicateSubtree(valuesExpr)

	// Verify both column references map to the same new column ID.
	dupValues := duplicated.(*memo.ValuesExpr)
	require.Equal(t, dupValues.Cols[0], dupValues.Cols[1], "duplicate column references should map to same new ID")

	// Verify the duplicated column ID is different from the original.
	require.NotEqual(t, colID, dupValues.Cols[0], "duplicated column ID should be different from original")
}

// TestDuplicateSubtreeRecursive verifies that nested expressions are
// duplicated correctly.
func TestDuplicateSubtreeRecursive(t *testing.T) {
	evalCtx := eval.MakeTestingEvalContext(cluster.MakeTestingClusterSettings())
	catalog := testcat.New()
	_, err := catalog.ExecuteDDL("CREATE TABLE t (a INT PRIMARY KEY, b INT)")
	require.NoError(t, err)

	var f norm.Factory
	f.Init(context.Background(), &evalCtx, catalog)

	// Create a scan expression.
	tn := tree.NewUnqualifiedTableName("t")
	tab := catalog.Table(tn)
	tabID := f.Metadata().AddTable(tab, tn)

	scanPrivate := &memo.ScanPrivate{Table: tabID}
	for i, n := 0, tab.ColumnCount(); i < n; i++ {
		colID := tabID.ColumnID(i)
		scanPrivate.Cols.Add(colID)
	}
	scanExpr := f.ConstructScan(scanPrivate)

	// Create a select on top of the scan with a filter referencing column a.
	colA := tabID.ColumnID(0)
	constExpr := f.ConstructConst(tree.NewDInt(5), types.Int)
	eqExpr := f.ConstructEq(f.ConstructVariable(colA), constExpr)
	filters := memo.FiltersExpr{f.ConstructFiltersItem(eqExpr)}
	selectExpr := f.ConstructSelect(scanExpr, filters)

	// Duplicate the select expression.
	duplicated := f.DuplicateSubtree(selectExpr)

	// Verify the duplicated select has different IDs.
	origSelect := selectExpr.(*memo.SelectExpr)
	dupSelect := duplicated.(*memo.SelectExpr)

	// Check that the table ID in the nested scan is different.
	origScan := origSelect.Input.(*memo.ScanExpr)
	dupScan := dupSelect.Input.(*memo.ScanExpr)
	require.NotEqual(t, origScan.Table, dupScan.Table, "nested scan should have different table ID")

	// Check that the column ID in the filter is different.
	origFilter := origSelect.Filters[0].Condition.(*memo.EqExpr)
	dupFilter := dupSelect.Filters[0].Condition.(*memo.EqExpr)
	origVar := origFilter.Left.(*memo.VariableExpr)
	dupVar := dupFilter.Left.(*memo.VariableExpr)
	require.NotEqual(t, origVar.Col, dupVar.Col, "filter column ID should be different")

	// Verify the new column belongs to the new table.
	dupColMeta := f.Metadata().ColumnMeta(dupVar.Col)
	require.Equal(t, dupScan.Table, dupColMeta.Table, "duplicated column should belong to duplicated table")
}

// TestDuplicateSubtreeMultipleDuplications verifies that duplicating the same
// expression multiple times produces independent copies with different IDs.
func TestDuplicateSubtreeMultipleDuplications(t *testing.T) {
	evalCtx := eval.MakeTestingEvalContext(cluster.MakeTestingClusterSettings())
	var f norm.Factory
	f.Init(context.Background(), &evalCtx, nil /* catalog */)

	// Create a Values expression.
	colID := f.Metadata().AddColumn("a", types.Int)
	cols := opt.ColList{colID}
	tupType := types.MakeTuple([]*types.T{types.Int})

	constExpr := f.ConstructConst(tree.NewDInt(1), types.Int)
	tuple := f.ConstructTuple(memo.ScalarListExpr{constExpr}, tupType)
	rows := memo.ScalarListExpr{tuple}

	valuesExpr := f.ConstructValues(rows, &memo.ValuesPrivate{
		Cols: cols,
		ID:   f.Metadata().NextUniqueID(),
	})

	// Duplicate the expression twice.
	dup1 := f.DuplicateSubtree(valuesExpr)
	dup2 := f.DuplicateSubtree(valuesExpr)

	// Verify each duplication has a different column ID.
	origValues := valuesExpr.(*memo.ValuesExpr)
	dupValues1 := dup1.(*memo.ValuesExpr)
	dupValues2 := dup2.(*memo.ValuesExpr)

	require.NotEqual(t, origValues.Cols[0], dupValues1.Cols[0], "first duplicate should have different ID")
	require.NotEqual(t, origValues.Cols[0], dupValues2.Cols[0], "second duplicate should have different ID")
	require.NotEqual(t, dupValues1.Cols[0], dupValues2.Cols[0], "duplicates should have different IDs from each other")
}

// TestDuplicateSubtreeSynthesizedColumns verifies that synthesized columns
// (those not belonging to a table) get fresh arbitrary column IDs.
func TestDuplicateSubtreeSynthesizedColumns(t *testing.T) {
	evalCtx := eval.MakeTestingEvalContext(cluster.MakeTestingClusterSettings())
	var f norm.Factory
	f.Init(context.Background(), &evalCtx, nil /* catalog */)

	// Create a Values expression with a synthesized column (not from a table).
	synColID := f.Metadata().AddColumn("synthesized", types.Int)
	cols := opt.ColList{synColID}
	tupType := types.MakeTuple([]*types.T{types.Int})

	constExpr := f.ConstructConst(tree.NewDInt(1), types.Int)
	tuple := f.ConstructTuple(memo.ScalarListExpr{constExpr}, tupType)
	rows := memo.ScalarListExpr{tuple}

	valuesExpr := f.ConstructValues(rows, &memo.ValuesPrivate{
		Cols: cols,
		ID:   f.Metadata().NextUniqueID(),
	})

	// Duplicate the expression.
	duplicated := f.DuplicateSubtree(valuesExpr)

	// Verify the duplicated column is different and also synthesized.
	origValues := valuesExpr.(*memo.ValuesExpr)
	dupValues := duplicated.(*memo.ValuesExpr)
	require.NotEqual(t, origValues.Cols[0], dupValues.Cols[0], "duplicated synthesized column should be different")

	// Verify both columns have no table association.
	origMeta := f.Metadata().ColumnMeta(origValues.Cols[0])
	dupMeta := f.Metadata().ColumnMeta(dupValues.Cols[0])
	require.Equal(t, opt.TableID(0), origMeta.Table, "original column should not belong to a table")
	require.Equal(t, opt.TableID(0), dupMeta.Table, "duplicated column should not belong to a table")
}

// TestDuplicateSubtreeUniqueIDs verifies that UniqueID fields get fresh IDs.
func TestDuplicateSubtreeUniqueIDs(t *testing.T) {
	evalCtx := eval.MakeTestingEvalContext(cluster.MakeTestingClusterSettings())
	var f norm.Factory
	f.Init(context.Background(), &evalCtx, nil /* catalog */)

	// Create a Values expression with a UniqueID.
	colID := f.Metadata().AddColumn("a", types.Int)
	cols := opt.ColList{colID}
	tupType := types.MakeTuple([]*types.T{types.Int})

	// Create a single row.
	constExpr := f.ConstructConst(tree.NewDInt(1), types.Int)
	tuple := f.ConstructTuple(memo.ScalarListExpr{constExpr}, tupType)
	rows := memo.ScalarListExpr{tuple}

	valuesExpr := f.ConstructValues(rows, &memo.ValuesPrivate{
		Cols: cols,
		ID:   f.Metadata().NextUniqueID(),
	})

	// Duplicate the Values expression.
	duplicated := f.DuplicateSubtree(valuesExpr)

	// Verify the duplicated expression has a different UniqueID.
	origValues := valuesExpr.(*memo.ValuesExpr)
	dupValues := duplicated.(*memo.ValuesExpr)
	require.NotEqual(t, origValues.ID, dupValues.ID, "duplicated UniqueID should be different")
}

// TestDuplicateSubtreeWithCTE verifies that CTEs are duplicated correctly
// with new WithIDs and bindings.
func TestDuplicateSubtreeWithCTE(t *testing.T) {
	evalCtx := eval.MakeTestingEvalContext(cluster.MakeTestingClusterSettings())
	var f norm.Factory
	f.Init(context.Background(), &evalCtx, nil /* catalog */)
	// Disable optimizations so the With expression isn't normalized away.
	f.DisableOptimizations()

	// Create a simple CTE binding - a Values expression.
	bindingColID := f.Metadata().AddColumn("x", types.Int)
	bindingCols := opt.ColList{bindingColID}
	tupType := types.MakeTuple([]*types.T{types.Int})

	constExpr := f.ConstructConst(tree.NewDInt(42), types.Int)
	tuple := f.ConstructTuple(memo.ScalarListExpr{constExpr}, tupType)
	rows := memo.ScalarListExpr{tuple}

	binding := f.ConstructValues(rows, &memo.ValuesPrivate{
		Cols: bindingCols,
		ID:   f.Metadata().NextUniqueID(),
	})

	// Create WithID and add binding to metadata.
	origWithID := f.Memo().NextWithID()
	f.Metadata().AddWithBinding(origWithID, binding)

	// Create a WithScan that references the CTE.
	scanColID := f.Metadata().AddColumn("y", types.Int)
	scanCols := opt.ColList{scanColID}

	withScan := f.ConstructWithScan(&memo.WithScanPrivate{
		With:    origWithID,
		Name:    "cte",
		InCols:  bindingCols,
		OutCols: scanCols,
		ID:      f.Metadata().NextUniqueID(),
	})

	// Create the With expression.
	withExpr := f.ConstructWith(binding, withScan, &memo.WithPrivate{
		ID:   origWithID,
		Name: "cte",
	})

	// Duplicate the With expression.
	duplicated := f.DuplicateSubtree(withExpr)

	// Verify the duplicated With has a different WithID.
	origWith := withExpr.(*memo.WithExpr)
	dupWith := duplicated.(*memo.WithExpr)
	require.NotEqual(t, origWith.ID, dupWith.ID, "duplicated WithID should be different")

	// Verify the duplicated binding has different column IDs.
	origBinding := origWith.Binding.(*memo.ValuesExpr)
	dupBinding := dupWith.Binding.(*memo.ValuesExpr)
	require.NotEqual(t, origBinding.Cols[0], dupBinding.Cols[0], "duplicated binding column should be different")

	// Verify the WithScan in Main references the new WithID.
	dupScan := dupWith.Main.(*memo.WithScanExpr)
	require.Equal(t, dupWith.ID, dupScan.With, "duplicated WithScan should reference new WithID")

	// Verify the duplicated WithScan has different output columns.
	origScan := origWith.Main.(*memo.WithScanExpr)
	require.NotEqual(t, origScan.OutCols[0], dupScan.OutCols[0], "duplicated scan output column should be different")

	// Verify the new binding is in metadata.
	require.NotPanics(t, func() {
		f.Metadata().WithBinding(dupWith.ID)
	})
}

// TestDuplicateSubtreeOuterColumns verifies that outer column references
// (columns not in any output set) are not remapped.
func TestDuplicateSubtreeOuterColumns(t *testing.T) {
	evalCtx := eval.MakeTestingEvalContext(cluster.MakeTestingClusterSettings())
	catalog := testcat.New()
	_, err := catalog.ExecuteDDL("CREATE TABLE t (a INT PRIMARY KEY, b INT)")
	require.NoError(t, err)

	var f norm.Factory
	f.Init(context.Background(), &evalCtx, catalog)

	// Create a scan expression.
	tn := tree.NewUnqualifiedTableName("t")
	tab := catalog.Table(tn)
	tabID := f.Metadata().AddTable(tab, tn)

	scanPrivate := &memo.ScanPrivate{Table: tabID}
	for i, n := 0, tab.ColumnCount(); i < n; i++ {
		colID := tabID.ColumnID(i)
		scanPrivate.Cols.Add(colID)
	}
	scanExpr := f.ConstructScan(scanPrivate)

	// Get column IDs.
	colA := tabID.ColumnID(0) // a

	// Create a filter that references column 'a' (from scan output) and
	// an outer column 'x' (not from scan).
	outerCol := f.Metadata().AddColumn("x", types.Int)
	varA := f.ConstructVariable(colA)
	varOuter := f.ConstructVariable(outerCol)
	eqExpr := f.ConstructEq(varA, varOuter)
	filters := memo.FiltersExpr{f.ConstructFiltersItem(eqExpr)}

	selectExpr := f.ConstructSelect(scanExpr, filters)

	// Duplicate the select expression.
	duplicated := f.DuplicateSubtree(selectExpr)

	// Verify the select and scan have different table and column IDs.
	origSelect := selectExpr.(*memo.SelectExpr)
	dupSelect := duplicated.(*memo.SelectExpr)

	origScan := origSelect.Input.(*memo.ScanExpr)
	dupScan := dupSelect.Input.(*memo.ScanExpr)
	require.NotEqual(t, origScan.Table, dupScan.Table, "duplicated scan should have different table")

	// Verify the filter's column 'a' reference was remapped.
	origFilter := origSelect.Filters[0].Condition.(*memo.EqExpr)
	dupFilter := dupSelect.Filters[0].Condition.(*memo.EqExpr)

	origVarA := origFilter.Left.(*memo.VariableExpr)
	dupVarA := dupFilter.Left.(*memo.VariableExpr)
	require.NotEqual(t, origVarA.Col, dupVarA.Col, "column 'a' from scan should be remapped")

	// Verify the outer column reference was NOT remapped.
	origVarOuter := origFilter.Right.(*memo.VariableExpr)
	dupVarOuter := dupFilter.Right.(*memo.VariableExpr)
	require.Equal(t, origVarOuter.Col, dupVarOuter.Col, "outer column should not be remapped")
	require.Equal(t, outerCol, dupVarOuter.Col, "outer column should be unchanged")
}
