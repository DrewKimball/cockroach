// Copyright 2024 The Cockroach Authors.
//
// Use of this software is governed by the Business Source License
// included in the file licenses/BSL.txt.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0, included in the file
// licenses/APL.txt.

package norm

import (
	"github.com/cockroachdb/cockroach/pkg/sql/opt"
	"github.com/cockroachdb/cockroach/pkg/sql/opt/memo"
	"github.com/cockroachdb/cockroach/pkg/util/intsets"
)

// GetUsedDispatchBranches returns the indices of all branches that are
// transitively referenced by the input expression via Dispatch expressions.
func (c *CustomFuncs) GetUsedDispatchBranches(
	input opt.ScalarExpr, private *memo.DispatcherPrivate,
) intsets.Fast {
	var found, prev intsets.Fast
	var findDispatches func(expr opt.Expr)
	findDispatches = func(expr opt.Expr) {
		if dispatch, ok := expr.(*memo.DispatchExpr); ok && dispatch.Dispatcher == private.ID {
			found.Add(dispatch.Branch)
		}
		for i := 0; i < expr.ChildCount(); i++ {
			findDispatches(expr.Child(i))
		}
	}
	findDispatches(input)
	if found.Len() > 0 {
		for {
			for branchID, def := range private.Branches {
				if found.Contains(branchID) && !prev.Contains(branchID) {
					for _, expr := range def.Body {
						findDispatches(expr)
					}
				}
			}
			if prev.Len() == found.Len() {
				// No new branches were found.
				break
			}
			prev.CopyFrom(found)
		}
	}
	return found
}

// DispatcherHasUnusedBranches returns true if the Dispatcher has any branches
// that are not referenced transitively through the input expression, as
// determined by the given "usedBranches" set of branch indices.
func (c *CustomFuncs) DispatcherHasUnusedBranches(
	private *memo.DispatcherPrivate, usedBranches intsets.Fast,
) bool {
	for i := range private.Branches {
		if private.Branches[i] != nil && !usedBranches.Contains(i) {
			return true
		}
	}
	return false
}

// RemoveUnusedDispatchBranches removes branches from the dispatcher when they
// are not referenced from the input expression or (transitively) through any of
// the branches it references. Note that the branch is set to nil rather than
// shifting the slice elements, since the branch indices need to remain stable.
func (c *CustomFuncs) RemoveUnusedDispatchBranches(
	private *memo.DispatcherPrivate, usedBranches intsets.Fast,
) *memo.DispatcherPrivate {
	newBranches := make(memo.RoutineDefList, len(private.Branches))
	copy(newBranches, private.Branches)
	for i := range newBranches {
		if !usedBranches.Contains(i) {
			newBranches[i] = nil
		}
	}
	return &memo.DispatcherPrivate{
		ID:       private.ID,
		Branches: newBranches,
		Typ:      private.Typ,
	}
}

// CanRemoveDispatcher returns true if the DispatcherExpr can be replaced with
// its input expression. This is the case when all of its branches have been
// inlined into the input expression.
func (c *CustomFuncs) CanRemoveDispatcher(private *memo.DispatcherPrivate) bool {
	for i := range private.Branches {
		if private.Branches[i] != nil {
			return false
		}
	}
	return true
}
