// Copyright 2026 The Cockroach Authors.
//
// Use of this software is governed by the CockroachDB Software License
// included in the /LICENSE file.

package opttester

import (
	"github.com/cockroachdb/cockroach/pkg/sql/opt"
	"github.com/cockroachdb/cockroach/pkg/sql/opt/memo"
	"github.com/cockroachdb/cockroach/pkg/sql/opt/norm"
	"github.com/cockroachdb/errors"
)

// duplicateValidator validates that a duplicated expression tree has all the
// correct properties: fresh IDs, consistent mappings, proper outer references, etc.
type duplicateValidator struct {
	f *norm.Factory

	// Analysis results from the original tree.
	analysis treeAnalysis

	// Discovered mappings during validation.
	colMap      map[opt.ColumnID]opt.ColumnID
	tableMap    map[opt.TableID]opt.TableID
	withMap     map[opt.WithID]opt.WithID
	seenUniques map[opt.UniqueID]struct{}
}

// treeAnalysis holds the results of analyzing the original tree to determine
// which IDs are internal (should be remapped) vs external (should be unchanged).
type treeAnalysis struct {
	// Columns that are internal to the subtree (should be remapped).
	innerCols opt.ColSet

	// Tables that are internal to the subtree (should be remapped).
	innerTables map[opt.TableID]struct{}

	// CTEs defined within the subtree (should be remapped).
	innerWiths map[opt.WithID]struct{}
}

func newDuplicateValidator(f *norm.Factory) *duplicateValidator {
	return &duplicateValidator{
		f:           f,
		colMap:      make(map[opt.ColumnID]opt.ColumnID),
		tableMap:    make(map[opt.TableID]opt.TableID),
		withMap:     make(map[opt.WithID]opt.WithID),
		seenUniques: make(map[opt.UniqueID]struct{}),
	}
}

// validate performs two-pass validation:
// 1. Analyze the original tree to determine inner vs outer IDs
// 2. Validate the duplicate tree against the original
func (v *duplicateValidator) validate(orig, dup opt.Expr) error {
	// Pass 1: Analyze the original tree.
	v.analysis = v.analyzeTree(orig)

	// Pass 2: Validate the duplicate tree.
	return v.validateExpr(orig, dup)
}

// analyzeTree walks the original tree to determine which IDs are internal.
func (v *duplicateValidator) analyzeTree(e opt.Expr) treeAnalysis {
	analysis := treeAnalysis{
		innerTables: make(map[opt.TableID]struct{}),
		innerWiths:  make(map[opt.WithID]struct{}),
	}

	var walk func(opt.Expr)
	walk = func(e opt.Expr) {
		// Collect output columns from relational expressions.
		if rel, ok := e.(memo.RelExpr); ok {
			analysis.innerCols.UnionWith(rel.Relational().OutputCols)
		}

		// Collect TableIDs and WithIDs from expressions.
		switch t := e.(type) {
		case *memo.ScanExpr:
			analysis.innerTables[t.Table] = struct{}{}
			// Register all columns from this table as inner.
			tabMeta := v.f.Metadata().TableMeta(t.Table)
			for i := 0; i < tabMeta.Table.ColumnCount(); i++ {
				analysis.innerCols.Add(t.Table.ColumnID(i))
			}

		case *memo.WithExpr:
			analysis.innerWiths[t.ID] = struct{}{}

		case *memo.RecursiveCTEExpr:
			analysis.innerWiths[t.WithID] = struct{}{}

		case *memo.InsertExpr:
			if t.WithID != 0 {
				analysis.innerWiths[t.WithID] = struct{}{}
			}

		case *memo.UpdateExpr:
			if t.WithID != 0 {
				analysis.innerWiths[t.WithID] = struct{}{}
			}

		case *memo.UpsertExpr:
			if t.WithID != 0 {
				analysis.innerWiths[t.WithID] = struct{}{}
			}

		case *memo.DeleteExpr:
			if t.WithID != 0 {
				analysis.innerWiths[t.WithID] = struct{}{}
			}
		}

		// Recurse on children.
		for i, n := 0, e.ChildCount(); i < n; i++ {
			walk(e.Child(i))
		}
	}

	walk(e)
	return analysis
}

// validateExpr recursively validates that orig and dup have the same structure
// and that all IDs are properly remapped or unchanged as expected.
func (v *duplicateValidator) validateExpr(orig, dup opt.Expr) error {
	// Check same operator type.
	if orig.Op() != dup.Op() {
		return errors.Errorf("operators should match: got %s vs %s", orig.Op(), dup.Op())
	}

	// Validate IDs based on expression type.
	if err := v.validateIDs(orig, dup); err != nil {
		return err
	}

	// Recursively validate children.
	if orig.ChildCount() != dup.ChildCount() {
		return errors.Errorf("child count should match: got %d vs %d", orig.ChildCount(), dup.ChildCount())
	}
	for i, n := 0, orig.ChildCount(); i < n; i++ {
		if err := v.validateExpr(orig.Child(i), dup.Child(i)); err != nil {
			return err
		}
	}

	return nil
}

// validateIDs validates ID fields for the given expression pair.
func (v *duplicateValidator) validateIDs(orig, dup opt.Expr) error {
	switch origTyped := orig.(type) {
	case *memo.VariableExpr:
		dupTyped := dup.(*memo.VariableExpr)
		return v.checkColumnID(origTyped.Col, dupTyped.Col)

	case *memo.ScanExpr:
		dupTyped := dup.(*memo.ScanExpr)
		if err := v.checkTableID(origTyped.Table, dupTyped.Table); err != nil {
			return err
		}
		return v.checkColSet(origTyped.Cols, dupTyped.Cols)

	case *memo.SelectExpr:
		// No ID fields to validate.
		return nil

	case *memo.ValuesExpr:
		dupTyped := dup.(*memo.ValuesExpr)
		if err := v.checkColList(origTyped.Cols, dupTyped.Cols); err != nil {
			return err
		}
		return v.checkUniqueID(origTyped.ID, dupTyped.ID)

	case *memo.WithExpr:
		dupTyped := dup.(*memo.WithExpr)
		return v.checkWithID(origTyped.ID, dupTyped.ID)

	case *memo.WithScanExpr:
		dupTyped := dup.(*memo.WithScanExpr)
		if err := v.checkWithID(origTyped.With, dupTyped.With); err != nil {
			return err
		}
		if err := v.checkColList(origTyped.InCols, dupTyped.InCols); err != nil {
			return err
		}
		if err := v.checkColList(origTyped.OutCols, dupTyped.OutCols); err != nil {
			return err
		}
		return v.checkUniqueID(origTyped.ID, dupTyped.ID)

	case *memo.ProjectionsItem:
		dupTyped := dup.(*memo.ProjectionsItem)
		return v.checkColumnID(origTyped.Col, dupTyped.Col)

	case *memo.AggregationsItem:
		dupTyped := dup.(*memo.AggregationsItem)
		return v.checkColumnID(origTyped.Col, dupTyped.Col)

	case *memo.FiltersItem:
		// No ID fields to validate.
		return nil

	default:
		// Most expression types don't have ID fields that need validation.
		// Only expressions with ColumnID, TableID, WithID, or UniqueID fields
		// need explicit cases above. Everything else can pass through.
		return nil
	}
}

// checkColumnID verifies that a column ID is correctly remapped or unchanged.
func (v *duplicateValidator) checkColumnID(orig, dup opt.ColumnID) error {
	isInner := v.analysis.innerCols.Contains(orig)

	if isInner {
		// Inner column - must be remapped.
		if orig == dup {
			return errors.Errorf("inner column %d should be remapped", orig)
		}

		// Check consistency.
		if existing, ok := v.colMap[orig]; ok {
			if existing != dup {
				return errors.Errorf("column %d should map consistently to %d, got %d", orig, existing, dup)
			}
		} else {
			v.colMap[orig] = dup
		}
	} else {
		// Outer column - must be unchanged.
		if orig != dup {
			return errors.Errorf("outer column %d should be unchanged, got %d", orig, dup)
		}
	}

	return nil
}

// checkTableID verifies that a table ID is correctly remapped or unchanged.
func (v *duplicateValidator) checkTableID(orig, dup opt.TableID) error {
	_, isInner := v.analysis.innerTables[orig]

	if isInner {
		// Inner table - must be remapped.
		if orig == dup {
			return errors.Errorf("inner table %d should be remapped", orig)
		}

		// Check consistency.
		if existing, ok := v.tableMap[orig]; ok {
			if existing != dup {
				return errors.Errorf("table %d should map consistently to %d, got %d", orig, existing, dup)
			}
		} else {
			v.tableMap[orig] = dup
		}
	} else {
		// External table - must be unchanged.
		if orig != dup {
			return errors.Errorf("external table %d should be unchanged, got %d", orig, dup)
		}
	}

	return nil
}

// checkWithID verifies that a WithID is correctly remapped or unchanged.
func (v *duplicateValidator) checkWithID(orig, dup opt.WithID) error {
	_, isInner := v.analysis.innerWiths[orig]

	if isInner {
		// Inner CTE - must be remapped.
		if orig == dup {
			return errors.Errorf("inner CTE %d should be remapped", orig)
		}

		// Check consistency.
		if existing, ok := v.withMap[orig]; ok {
			if existing != dup {
				return errors.Errorf("WithID %d should map consistently to %d, got %d", orig, existing, dup)
			}
		} else {
			v.withMap[orig] = dup
		}
	} else {
		// External CTE - must be unchanged.
		if orig != dup {
			return errors.Errorf("external CTE %d should be unchanged, got %d", orig, dup)
		}
	}

	return nil
}

// checkUniqueID verifies that a UniqueID is always fresh (never reused).
func (v *duplicateValidator) checkUniqueID(orig, dup opt.UniqueID) error {
	// UniqueIDs must always be remapped.
	if orig == dup {
		return errors.Errorf("UniqueID %d should always be fresh", orig)
	}

	// Check that we haven't seen this duplicate ID before.
	if _, seen := v.seenUniques[dup]; seen {
		return errors.Errorf("duplicate UniqueID %d was already used", dup)
	}
	v.seenUniques[dup] = struct{}{}

	return nil
}

// checkColSet verifies that all columns in a ColSet are correctly remapped.
func (v *duplicateValidator) checkColSet(orig, dup opt.ColSet) error {
	if orig.Len() != dup.Len() {
		return errors.Errorf("ColSet should have same size: got %d vs %d", orig.Len(), dup.Len())
	}

	origCols := orig.ToList()
	dupCols := dup.ToList()
	if len(origCols) != len(dupCols) {
		return errors.Errorf("ColSet lists should have same length: got %d vs %d", len(origCols), len(dupCols))
	}

	for i := range origCols {
		if err := v.checkColumnID(origCols[i], dupCols[i]); err != nil {
			return err
		}
	}

	return nil
}

// checkColList verifies that all columns in a ColList are correctly remapped.
func (v *duplicateValidator) checkColList(orig, dup opt.ColList) error {
	if len(orig) != len(dup) {
		return errors.Errorf("ColList should have same length: got %d vs %d", len(orig), len(dup))
	}

	for i := range orig {
		if err := v.checkColumnID(orig[i], dup[i]); err != nil {
			return errors.Wrapf(err, "at index %d", i)
		}
	}

	return nil
}
