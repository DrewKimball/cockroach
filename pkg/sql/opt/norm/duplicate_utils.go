// Copyright 2026 The Cockroach Authors.
//
// Use of this software is governed by the CockroachDB Software License
// included in the /LICENSE file.

package norm

import (
	"github.com/cockroachdb/cockroach/pkg/sql/opt"
	"github.com/cockroachdb/errors"
)

// subtreeDuplicator duplicates expression subtrees with fresh column and table IDs.
// This is used for inlining subtrees in multiple places (CTEs, routines, subqueries)
// where conflicting column IDs would otherwise cause issues.
//
// Column and table IDs are allocated dynamically as the subtree is traversed,
// building up the mapping on the fly. The same source ID always maps to the same
// destination ID within a single duplication operation.
//
// Columns that are not in the output columns of any expression in the subtree are
// considered "outer" references and are not remapped.
type subtreeDuplicator struct {
	f  *Factory
	md *opt.Metadata

	// Dynamically built mappings as we traverse
	colMap   map[opt.ColumnID]opt.ColumnID
	tableMap map[opt.TableID]opt.TableID
	withMap  map[opt.WithID]opt.WithID
}

// DuplicateColumnID returns the remapped column ID for the given ID.
// If this ID was not registered (via registerOutputColumns), it's an outer
// column reference and is returned unchanged.
// This method is exported to implement the opt.ColumnIDDuplicator interface.
func (d *subtreeDuplicator) DuplicateColumnID(id opt.ColumnID) opt.ColumnID {
	if newID, ok := d.colMap[id]; ok {
		return newID
	}
	// Not mapped - this is an outer column reference, leave unchanged.
	return id
}

// DuplicateTableID allocates a fresh table ID for the given ID.
// If this ID was seen before, returns the previously allocated ID.
func (d *subtreeDuplicator) DuplicateTableID(id opt.TableID) opt.TableID {
	if newID, ok := d.tableMap[id]; ok {
		return newID
	}
	// Allocate fresh table ID - we don't need expression remapping for the
	// table metadata itself since we'll be duplicating all expressions that
	// reference these tables.
	newID := d.md.DuplicateTable(id, nil /* no expression remapping needed */)
	d.tableMap[id] = newID
	return newID
}

// DuplicateUniqueID allocates a fresh unique ID.
// Unlike column and table IDs, unique IDs are never memoized - we always
// allocate a fresh ID to ensure uniqueness.
func (d *subtreeDuplicator) DuplicateUniqueID(id opt.UniqueID) opt.UniqueID {
	return d.md.NextUniqueID()
}

// DuplicateWithID returns the remapped WithID for the given ID.
// If this CTE was duplicated (internal to the subtree), returns the new WithID.
// If not mapped, this references an external CTE and is returned unchanged.
func (d *subtreeDuplicator) DuplicateWithID(id opt.WithID) opt.WithID {
	if newID, ok := d.withMap[id]; ok {
		return newID
	}
	// Not mapped - this references an external CTE, leave unchanged.
	return id
}

// registerTable duplicates a table and creates column ID mappings for all
// columns in that table. This must be called before duplicating fields that
// reference table columns (e.g., scans can reference columns they don't output).
func (d *subtreeDuplicator) registerTable(tableID opt.TableID) {
	if _, ok := d.tableMap[tableID]; ok {
		return // already registered
	}

	// Duplicate the table.
	newTableID := d.DuplicateTableID(tableID)

	// Register all columns from this table.
	tableMeta := d.md.TableMeta(tableID)
	for i := 0; i < tableMeta.Table.ColumnCount(); i++ {
		oldColID := tableID.ColumnID(i)
		newColID := newTableID.ColumnID(i)
		d.colMap[oldColID] = newColID
	}
}

// registerOutputColumn creates a column ID mapping for a single synthesized
// column (one with no table). If the column belongs to a table, registerTable
// should be called instead.
func (d *subtreeDuplicator) registerOutputColumn(col opt.ColumnID) {
	if _, ok := d.colMap[col]; ok {
		return // already mapped
	}

	colMeta := d.md.ColumnMeta(col)
	if colMeta.Table != 0 {
		panic(errors.AssertionFailedf(
			"registerOutputColumn called for table column %d; use registerTable instead",
			col,
		))
	}

	// Synthesized column - create a new one with the same alias and type.
	newID := d.md.AddColumn(colMeta.Alias, colMeta.Type)
	d.colMap[col] = newID
}

// registerOutputColumns creates column ID mappings for all columns in the
// given set. This must be called for each relational expression's output
// columns before duplicating its fields.
//
// For columns that belong to a table, the entire table is registered (if not
// already). For synthesized columns, individual mappings are created.
func (d *subtreeDuplicator) registerOutputColumns(cols opt.ColSet) {
	cols.ForEach(func(col opt.ColumnID) {
		if _, ok := d.colMap[col]; ok {
			return // already mapped
		}

		colMeta := d.md.ColumnMeta(col)
		if colMeta.Table != 0 {
			// Column from a table - register the entire table.
			d.registerTable(colMeta.Table)
		} else {
			// Synthesized column.
			d.registerOutputColumn(col)
		}
	})
}
