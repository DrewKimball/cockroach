// Copyright 2026 The Cockroach Authors.
//
// Use of this software is governed by the CockroachDB Software License
// included in the /LICENSE file.

package main

import (
	"fmt"
	"io"

	"github.com/cockroachdb/cockroach/pkg/sql/opt/optgen/lang"
)

// duplicateGen generates the subtree duplication code that creates copies
// of expression subtrees with fresh column and table IDs.
type duplicateGen struct {
	compiled *lang.CompiledExpr
	md       *metadata
	w        *matchWriter
}

func (g *duplicateGen) generate(compiled *lang.CompiledExpr, w io.Writer) {
	g.compiled = compiled
	g.md = newMetadata(compiled, "norm")
	g.w = &matchWriter{writer: w}

	g.w.writeIndent("package norm\n\n")

	g.w.nestIndent("import (\n")
	g.w.writeIndent("\n")
	g.w.writeIndent("\"github.com/cockroachdb/cockroach/pkg/sql/opt\"\n")
	g.w.writeIndent("\"github.com/cockroachdb/cockroach/pkg/sql/opt/memo\"\n")
	g.w.writeIndent("\"github.com/cockroachdb/errors\"\n")
	g.w.unnest(")\n\n")

	// Generate duplicate methods for Private structs.
	privates := g.compiled.Defines.WithTag("Private")
	for _, define := range privates {
		g.genPrivateDuplicate(define)
	}

	// Generate duplicate methods for List types.
	lists := g.compiled.Defines.WithTag("List")
	for _, define := range lists {
		g.genListDuplicate(define)
	}

	// Generate duplicate methods for expression types (Relational, Scalar, and ListItem).
	exprs := g.compiled.Defines.
		WithoutTag("Private").
		WithoutTag("List")
	for _, define := range exprs {
		g.genExprDuplicate(define)
	}

	// Generate the main dispatch method.
	g.genDuplicateExpr()
}

// genPrivateDuplicate generates a duplicate method for a Private struct.
// Example output:
//
//	func (d *subtreeDuplicator) duplicateScanPrivate(p *memo.ScanPrivate) *memo.ScanPrivate {
//	  return &memo.ScanPrivate{
//	    Table: d.duplicateTableID(p.Table),
//	    Cols: p.Cols.Duplicate(d),
//	    Index: p.Index,
//	    // ... other fields
//	  }
//	}
func (g *duplicateGen) genPrivateDuplicate(define *lang.DefineExpr) {
	privateTyp := g.md.typeOf(define)
	funcName := fmt.Sprintf("duplicate%s", define.Name)

	g.w.nestIndent("func (d *subtreeDuplicator) %s(p *%s) *%s {\n",
		funcName, privateTyp.name, privateTyp.name)

	g.w.nestIndent("return &%s{\n", privateTyp.name)

	for _, field := range define.Fields {
		fieldName := g.md.fieldName(field)
		fieldTyp := g.md.typeOf(field)
		g.w.writeIndent("%s: ", fieldName)
		g.genFieldDuplicate(field, "p."+fieldName, fieldTyp)
		g.w.write(",\n")
	}

	g.w.unnest("}\n")
	g.w.unnest("}\n\n")
}

// genListDuplicate generates a duplicate method for a List type.
// Example output:
//
//	func (d *subtreeDuplicator) duplicateFiltersExpr(list *memo.FiltersExpr) *memo.FiltersExpr {
//	  if list == nil || len(*list) == 0 {
//	    return list
//	  }
//	  newList := make(memo.FiltersExpr, len(*list))
//	  for i := range *list {
//	    newList[i] = d.duplicateFiltersItem(&(*list)[i])
//	  }
//	  result := memo.FiltersExpr(newList)
//	  return &result
//	}
func (g *duplicateGen) genListDuplicate(define *lang.DefineExpr) {
	listTyp := g.md.typeOf(define)
	itemTyp := listTyp.listItemType
	funcName := fmt.Sprintf("duplicate%s", listTyp.friendlyName)

	g.w.nestIndent("func (d *subtreeDuplicator) %s(list *%s) *%s {\n",
		funcName, listTyp.name, listTyp.name)

	g.w.nestIndent("if list == nil || len(*list) == 0 {\n")
	g.w.writeIndent("return list\n")
	g.w.unnest("}\n")

	g.w.writeIndent("newList := make(%s, len(*list))\n", listTyp.name)
	g.w.nestIndent("for i := range *list {\n")

	// Handle different list item types.
	if itemTyp.isInterface {
		// Interface types (e.g., opt.ScalarExpr) - duplicate directly.
		g.w.writeIndent("newList[i] = d.duplicateExpr((*list)[i])")
		if itemTyp.friendlyName != "Expr" {
			g.w.write(".(%s)", itemTyp.asParam())
		}
		g.w.write("\n")
	} else {
		// ListItem types (e.g., FiltersItem) - have pointer receivers but stored by value.
		g.w.writeIndent("item := d.duplicateExpr(&(*list)[i]).(*%s)\n", itemTyp.name)
		g.w.writeIndent("newList[i] = *item\n")
	}

	g.w.unnest("}\n")
	g.w.writeIndent("result := %s(newList)\n", listTyp.name)
	g.w.writeIndent("return &result\n")
	g.w.unnest("}\n\n")
}

// genExprDuplicate generates a duplicate method for an expression type.
// Example output:
//
//	func (d *subtreeDuplicator) duplicateSelectExpr(e *memo.SelectExpr) opt.Expr {
//	  newInput := d.duplicateExpr(e.Input).(memo.RelExpr)
//	  newFilters := d.duplicateFiltersExpr(&e.Filters)
//	  return d.f.ConstructSelect(newInput, *newFilters)
//	}
func (g *duplicateGen) genExprDuplicate(define *lang.DefineExpr) {
	exprTyp := g.md.typeOf(define)
	funcName := fmt.Sprintf("duplicate%s", define.Name)
	isEnforcer := define.Tags.Contains("Enforcer")
	isListItem := define.Tags.Contains("ListItem")
	isRelational := define.Tags.Contains("Relational")

	g.w.nestIndent("func (d *subtreeDuplicator) %s(e *%s) opt.Expr {\n",
		funcName, exprTyp.name)

	// Special handling for operators with the WithBinding tag.
	// These operators bind an expression and need special WithID handling.
	if define.Tags.Contains("WithBinding") {
		g.genWithBindingDuplicate(define)
		g.w.unnest("}\n\n")
		return
	}

	// For expressions with TableID fields in their private, register the table
	// first before duplicating fields. This ensures all table columns are mapped
	// before we encounter references to them.
	g.genRegisterTables(define)

	// Get all child and private fields.
	fields := g.md.childAndPrivateFields(define)

	// Duplicate child expressions first (not lists).
	// Child expressions will register their own output columns.
	childFields := g.md.childFields(define)
	for _, field := range childFields {
		fieldName := g.md.fieldName(field)
		fieldTyp := g.md.typeOf(field)
		varName := "new" + fieldName

		// Special handling for LiteralValues.Rows which needs a type assertion.
		needsTypeAssertion := define.Name == "LiteralValues" && fieldName == "Rows"

		// Skip list types for now - we'll duplicate them after registering output columns.
		if fieldTyp.isListType() {
			continue
		}

		g.w.writeIndent("%s := d.duplicateExpr(e.%s)", varName, fieldName)

		// Add type assertion if needed.
		if needsTypeAssertion {
			g.w.write(".(*opt.LiteralRows)")
		} else if fieldTyp.isInterface && fieldTyp.friendlyName != "Expr" {
			// Cast to the appropriate type if needed.
			g.w.write(".(%s)", fieldTyp.asParam())
		}
		g.w.write("\n")
	}

	// For relational expressions, register output columns now.
	// This must happen AFTER duplicating child expressions (which register their outputs)
	// but BEFORE duplicating list fields (which may reference these output columns).
	if isRelational {
		g.w.writeIndent("\n")
		g.w.writeIndent("// Register output columns for this expression.\n")
		g.w.writeIndent("d.registerOutputColumns(e.Relational().OutputCols)\n")
		g.w.writeIndent("\n")
	}

	// Now duplicate list fields (which may reference output columns).
	for _, field := range childFields {
		fieldName := g.md.fieldName(field)
		fieldTyp := g.md.typeOf(field)
		varName := "new" + fieldName

		// Only process list types here.
		if !fieldTyp.isListType() {
			continue
		}

		listDuplicateFunc := fmt.Sprintf("duplicate%s", fieldTyp.friendlyName)
		g.w.writeIndent("%s := d.%s(&e.%s)\n", varName, listDuplicateFunc, fieldName)
	}

	// Duplicate the private field if it exists.
	privateField := g.md.privateField(define)
	if privateField != nil {
		privateName := g.md.fieldName(privateField)
		privateTyp := g.md.typeOf(privateField)

		// Check if this is a Private struct type that needs duplication.
		// Generated private structs will have duplicate methods generated.
		if privateTyp.isGenerated && g.isPrivateStruct(privateTyp.friendlyName) {
			varName := "new" + privateName
			privateFuncName := fmt.Sprintf("duplicate%s", privateTyp.friendlyName)
			// Private fields are always pointers, so we pass &e.PrivateField.
			g.w.writeIndent("%s := d.%s(&e.%s)\n",
				varName, privateFuncName, privateName)
		}
	}

	// Construct the new expression.
	if isEnforcer {
		// Enforcer operators don't have factory constructors - build directly.
		g.w.nestIndent("return &%s{\n", exprTyp.name)
		for _, field := range fields {
			fieldName := g.md.fieldName(field)
			fieldTyp := g.md.typeOf(field)
			g.w.writeIndent("%s: ", fieldName)

			if fieldTyp.isExpr {
				// This is a child field - use the duplicated version.
				varName := "new" + fieldName
				// List types return pointers, so dereference them.
				if fieldTyp.isListType() {
					g.w.write("*%s", varName)
				} else {
					g.w.write("%s", varName)
				}
			} else if privateField != nil && field == privateField {
				// This is a private field.
				if fieldTyp.isGenerated && g.isPrivateStruct(fieldTyp.friendlyName) {
					// Private struct - use duplicated version (already a pointer).
					varName := "new" + fieldName
					g.w.write("*%s", varName)
				} else {
					// Other private field - duplicate inline.
					g.genFieldDuplicate(field, "e."+fieldName, fieldTyp)
				}
			} else {
				// Embedded or exported field - duplicate inline.
				g.genFieldDuplicate(field, "e."+fieldName, fieldTyp)
			}
			g.w.write(",\n")
		}
		g.w.unnest("}\n")
	} else {
		// Normal expression - use factory constructor.
		g.w.writeIndent("result := d.f.Construct%s(", define.Name)

		for i, field := range fields {
			if i > 0 {
				g.w.write(", ")
			}

			fieldName := g.md.fieldName(field)
			fieldTyp := g.md.typeOf(field)

			if fieldTyp.isExpr {
				// This is a child field - use the duplicated version.
				varName := "new" + fieldName
				// List types return pointers, so dereference them.
				if fieldTyp.isListType() {
					g.w.write("*%s", varName)
				} else {
					g.w.write("%s", varName)
				}
			} else if privateField != nil && field == privateField {
				// This is a private field.
				if fieldTyp.isGenerated && g.isPrivateStruct(fieldTyp.friendlyName) {
					// Private struct - use duplicated version (already a pointer).
					varName := "new" + fieldName
					g.w.write("%s", varName)
				} else {
					// Other private field - duplicate inline.
					g.genFieldDuplicate(field, "e."+fieldName, fieldTyp)
				}
			} else {
				// Embedded or exported field - duplicate inline.
				g.genFieldDuplicate(field, "e."+fieldName, fieldTyp)
			}
		}

		g.w.write(")\n")

		// ListItem types are returned by value but need to be returned as pointers.
		if isListItem {
			g.w.writeIndent("return &result\n")
		} else {
			g.w.writeIndent("return result\n")
		}
	}

	g.w.unnest("}\n\n")
}

// genWithBindingDuplicate generates duplication code for CTE expressions
// (With and RecursiveCTE) that bind an expression to a WithID.
func (g *duplicateGen) genWithBindingDuplicate(define *lang.DefineExpr) {
	opName := string(define.Name)

	switch opName {
	case "With":
		g.genWithDuplicate()
	case "RecursiveCTE":
		g.genRecursiveCTEDuplicate()
	default:
		// Mutation operators handled by genMutationDuplicate
		g.genMutationDuplicate(define)
	}
}

// genWithDuplicate generates duplication code for With expressions.
func (g *duplicateGen) genWithDuplicate() {
	g.w.writeIndent("// Allocate new WithID and record the mapping.\n")
	g.w.writeIndent("newWithID := d.f.Memo().NextWithID()\n")
	g.w.writeIndent("d.withMap[e.ID] = newWithID\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Duplicate the binding expression.\n")
	g.w.writeIndent("newBinding := d.duplicateExpr(e.Binding).(memo.RelExpr)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Add the binding to metadata so WithScans can reference it.\n")
	g.w.writeIndent("d.md.AddWithBinding(newWithID, newBinding)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Duplicate the main expression.\n")
	g.w.writeIndent("newMain := d.duplicateExpr(e.Main).(memo.RelExpr)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Register output columns.\n")
	g.w.writeIndent("d.registerOutputColumns(e.Relational().OutputCols)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Duplicate the private.\n")
	g.w.writeIndent("newPrivate := d.duplicateWithPrivate(&e.WithPrivate)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("return d.f.ConstructWith(newBinding, newMain, newPrivate)\n")
}

// genRecursiveCTEDuplicate generates duplication code for RecursiveCTE expressions.
func (g *duplicateGen) genRecursiveCTEDuplicate() {
	g.w.writeIndent("// Allocate new WithID and record the mapping.\n")
	g.w.writeIndent("newWithID := d.f.Memo().NextWithID()\n")
	g.w.writeIndent("d.withMap[e.WithID] = newWithID\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Duplicate non-recursive children (Binding and Initial).\n")
	g.w.writeIndent("newBinding := d.duplicateExpr(e.Binding).(memo.RelExpr)\n")
	g.w.writeIndent("newInitial := d.duplicateExpr(e.Initial).(memo.RelExpr)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Add binding to metadata before duplicating Recursive.\n")
	g.w.writeIndent("d.md.AddWithBinding(newWithID, newBinding)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Duplicate the recursive child (contains WithScans).\n")
	g.w.writeIndent("newRecursive := d.duplicateExpr(e.Recursive).(memo.RelExpr)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Register output columns.\n")
	g.w.writeIndent("d.registerOutputColumns(e.Relational().OutputCols)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Duplicate the private.\n")
	g.w.writeIndent("newPrivate := d.duplicateRecursiveCTEPrivate(&e.RecursiveCTEPrivate)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("return d.f.ConstructRecursiveCTE(newBinding, newInitial, newRecursive, newPrivate)\n")
}

// genMutationDuplicate generates duplication code for mutation operators
// (Insert, Update, Upsert, Delete) that may bind their input to a WithID.
func (g *duplicateGen) genMutationDuplicate(define *lang.DefineExpr) {
	g.w.writeIndent("// Register table columns.\n")
	g.w.writeIndent("d.registerTable(e.MutationPrivate.Table)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Duplicate the input.\n")
	g.w.writeIndent("newInput := d.duplicateExpr(e.Input).(memo.RelExpr)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// If the input is bound to a WithID, create a new binding.\n")
	g.w.nestIndent("if e.MutationPrivate.WithID != 0 {\n")
	g.w.writeIndent("newWithID := d.f.Memo().NextWithID()\n")
	g.w.writeIndent("d.withMap[e.MutationPrivate.WithID] = newWithID\n")
	g.w.writeIndent("d.md.AddWithBinding(newWithID, newInput)\n")
	g.w.unnest("}\n")
	g.w.writeIndent("\n")

	// Duplicate other child fields.
	childFields := g.md.childFields(define)
	for _, field := range childFields {
		fieldName := g.md.fieldName(field)
		if fieldName == "Input" {
			continue
		}
		fieldTyp := g.md.typeOf(field)
		varName := "new" + fieldName

		if fieldTyp.isListType() {
			listDuplicateFunc := fmt.Sprintf("duplicate%s", fieldTyp.friendlyName)
			g.w.writeIndent("%s := d.%s(&e.%s)\n", varName, listDuplicateFunc, fieldName)
		} else {
			g.w.writeIndent("%s := d.duplicateExpr(e.%s).(%s)\n", varName, fieldName, fieldTyp.asParam())
		}
	}

	if len(childFields) > 1 {
		g.w.writeIndent("\n")
	}

	g.w.writeIndent("// Register output columns.\n")
	g.w.writeIndent("d.registerOutputColumns(e.Relational().OutputCols)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Duplicate the private.\n")
	g.w.writeIndent("newPrivate := d.duplicateMutationPrivate(&e.MutationPrivate)\n")
	g.w.writeIndent("\n")

	// Construct the result.
	g.w.writeIndent("return d.f.Construct%s(", define.Name)
	fields := g.md.childAndPrivateFields(define)
	for i, field := range fields {
		if i > 0 {
			g.w.write(", ")
		}
		fieldName := g.md.fieldName(field)
		fieldTyp := g.md.typeOf(field)

		if fieldTyp.isExpr {
			varName := "new" + fieldName
			if fieldTyp.isListType() {
				g.w.write("*%s", varName)
			} else {
				g.w.write("%s", varName)
			}
		} else {
			g.w.write("newPrivate")
		}
	}
	g.w.write(")\n")
}

// genWithExprDuplicate is deprecated - use genWithBindingDuplicate instead.
// Kept for reference but not called.
func (g *duplicateGen) genWithExprDuplicate() {
	g.w.writeIndent("// Allocate new WithID and record the mapping.\n")
	g.w.writeIndent("newWithID := d.f.Memo().NextWithID()\n")
	g.w.writeIndent("d.withMap[e.ID] = newWithID\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Duplicate the binding expression.\n")
	g.w.writeIndent("newBinding := d.duplicateExpr(e.Binding).(memo.RelExpr)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Add the new binding to metadata.\n")
	g.w.writeIndent("d.md.AddWithBinding(newWithID, newBinding)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Duplicate the main expression (may contain WithScans referencing this CTE).\n")
	g.w.writeIndent("newMain := d.duplicateExpr(e.Main).(memo.RelExpr)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Register With's output columns AFTER duplicating children.\n")
	g.w.writeIndent("d.registerOutputColumns(e.Relational().OutputCols)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Duplicate the WithPrivate with new WithID.\n")
	g.w.writeIndent("newPrivate := d.duplicateWithPrivate(&e.WithPrivate)\n")
	g.w.writeIndent("\n")

	g.w.writeIndent("// Construct the new With expression.\n")
	g.w.writeIndent("return d.f.ConstructWith(newBinding, newMain, newPrivate)\n")
}

// genRegisterTables generates code to register tables for expressions that have
// TableID fields in their Private structs. This must be done before duplicating
// fields to ensure all table columns are mapped.
func (g *duplicateGen) genRegisterTables(define *lang.DefineExpr) {
	privateField := g.md.privateField(define)
	if privateField == nil {
		return
	}

	privateTyp := g.md.typeOf(privateField)
	if !privateTyp.isGenerated {
		return // Only look at generated Private structs
	}

	// Find the Private struct definition.
	var privateDefine *lang.DefineExpr
	for _, d := range g.compiled.Defines {
		if string(d.Name) == privateTyp.friendlyName {
			privateDefine = d
			break
		}
	}

	if privateDefine == nil {
		return
	}

	// Look for TableID fields in the Private struct.
	privateName := g.md.fieldName(privateField)
	for _, field := range privateDefine.Fields {
		fieldTyp := g.md.typeOf(field)
		if fieldTyp.friendlyName == "TableID" {
			fieldName := g.md.fieldName(field)
			g.w.writeIndent("// Register table to ensure all its columns are mapped.\n")
			g.w.writeIndent("d.registerTable(e.%s.%s)\n", privateName, fieldName)
			g.w.writeIndent("\n")
		}
	}
}

// genFieldDuplicate generates code to duplicate a single field based on its type.
func (g *duplicateGen) genFieldDuplicate(field *lang.DefineFieldExpr, fieldRef string, fieldTyp *typeDef) {
	switch fieldTyp.friendlyName {
	case "ColumnID":
		g.w.write("d.DuplicateColumnID(%s)", fieldRef)

	case "TableID":
		g.w.write("d.DuplicateTableID(%s)", fieldRef)

	case "UniqueID":
		g.w.write("d.DuplicateUniqueID(%s)", fieldRef)

	case "WithID":
		g.w.write("d.DuplicateWithID(%s)", fieldRef)

	case "ColSet":
		g.w.write("%s.Duplicate(d)", fieldRef)

	case "ColList":
		g.w.write("%s.Duplicate(d)", fieldRef)

	case "OptionalColList":
		g.w.write("%s.Duplicate(d)", fieldRef)

	case "Ordering":
		g.w.write("%s.Duplicate(d)", fieldRef)

	case "OrderingChoice":
		g.w.write("%s.Duplicate(d)", fieldRef)

	case "Presentation":
		g.w.write("%s.Duplicate(d)", fieldRef)

	case "RelPropsPtr":
		// Relational properties contain column IDs that must be remapped.
		g.w.write("d.duplicateRelProps(%s)", fieldRef)

	default:
		// For all other types (primitives, pointers, interfaces, etc.), copy as-is.
		// These types don't contain column or table IDs.
		g.w.write("%s", fieldRef)
	}
}

// isPrivateStruct checks if a type name refers to a Private struct defined
// in the .opt files.
func (g *duplicateGen) isPrivateStruct(typeName string) bool {
	for _, define := range g.compiled.Defines {
		if string(define.Name) == typeName && define.Tags.Contains("Private") {
			return true
		}
	}
	return false
}

// genDuplicateExpr generates the main dispatch method that routes to the
// appropriate duplicate function based on expression type.
func (g *duplicateGen) genDuplicateExpr() {
	g.w.writeIndent("// duplicateExpr duplicates an expression with fresh column and table IDs.\n")
	g.w.writeIndent("// This is the main internal dispatch method.\n")
	g.w.nestIndent("func (d *subtreeDuplicator) duplicateExpr(e opt.Expr) opt.Expr {\n")

	g.w.nestIndent("switch t := e.(type) {\n")

	// Generate cases for all expression types (including ListItem).
	exprs := g.compiled.Defines.
		WithoutTag("Private").
		WithoutTag("List")

	for _, define := range exprs {
		exprTyp := g.md.typeOf(define)
		funcName := fmt.Sprintf("duplicate%s", define.Name)

		g.w.writeIndent("case *%s:\n", exprTyp.name)
		g.w.writeIndent("\treturn d.%s(t)\n", funcName)
	}

	// Generate cases for List types. These are needed because some List types
	// like FiltersExpr implement ScalarExpr and can appear in table metadata
	// (e.g., partial index predicates).
	lists := g.compiled.Defines.WithTag("List")
	for _, define := range lists {
		listTyp := g.md.typeOf(define)
		funcName := fmt.Sprintf("duplicate%sExpr", define.Name)

		g.w.writeIndent("case *%s:\n", listTyp.name)
		g.w.writeIndent("\treturn d.%s(t)\n", funcName)
	}

	// Default case - panic for unhandled types.
	g.w.writeIndent("default:\n")
	g.w.writeIndent("\tpanic(errors.AssertionFailedf(\"unhandled expression type in DuplicateSubtree: %%T\", e))\n")

	g.w.unnest("}\n")
	g.w.unnest("}\n")
}
