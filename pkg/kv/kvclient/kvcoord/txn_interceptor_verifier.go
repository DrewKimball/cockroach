// Copyright 2025 The Cockroach Authors.
//
// Use of this software is governed by the CockroachDB Software License
// included in the /LICENSE file.

package kvcoord

import (
	"context"

	"github.com/cockroachdb/cockroach/pkg/kv/kvpb"
	"github.com/cockroachdb/cockroach/pkg/roachpb"
	"github.com/cockroachdb/cockroach/pkg/util/buildutil"
	"github.com/cockroachdb/cockroach/pkg/util/interval"
	"github.com/cockroachdb/cockroach/pkg/util/log"
	"github.com/cockroachdb/errors"
)

// txnVerifier provides verification logic for leaf transactions to ensure that
// they don't read outside the expected read spans. It is only used in test
// builds.
type txnVerifier struct {
	wrapped lockedSender

	// readsTree contains the allowed read spans for leaf transactions. If nil, no
	// verification is performed.
	readsTree interval.Tree
}

var _ txnInterceptor = &txnVerifier{}

// SendLocked implements the lockedSender interface.
func (tv *txnVerifier) SendLocked(
	ctx context.Context, ba *kvpb.BatchRequest,
) (*kvpb.BatchResponse, *kvpb.Error) {
	// Verify read requests don't go outside allowed spans for leaf transactions.
	if buildutil.CrdbTestBuild {
		if tv.readsTree != nil {
			if err := tv.verifyReadSpans(ba); err != nil {
				return nil, kvpb.NewError(err)
			}
		}
	}
	return tv.wrapped.SendLocked(ctx, ba)
}

// verifyReadSpans checks that all read requests in the batch are within
// the allowed read spans defined by readsTree.
func (tv *txnVerifier) verifyReadSpans(ba *kvpb.BatchRequest) error {
	for _, req := range ba.Requests {
		reqSpan := req.GetInner().Header().Span()
		if !kvpb.IsReadOnly(req.GetInner()) {
			// Currently, the txnVerifier and readsTree are only used for leaf txns,
			// in which case only read-only requests are expected.
			return errors.AssertionFailedf(
				"expected read-only requests for leaf txns, got %s", req.GetInner().Method())
		}
		if !reqSpan.Valid() {
			continue
		}

		// Check if the span overlaps with any allowed span in readsTree.
		endKey := []byte(reqSpan.EndKey)
		if len(endKey) == 0 {
			endKey = reqSpan.Key.Next()
		}
		spanRange := interval.Range{Start: []byte(reqSpan.Key), End: endKey}
		overlaps := tv.readsTree.DoMatching(
			func(interval.Interface) (done bool) { return true }, // Stop on first match
			spanRange,
		)
		if !overlaps {
			return errors.AssertionFailedf(
				"leaf transaction attempted to read outside allowed spans: request span %s not in readsTree",
				reqSpan)
		}
	}
	return nil
}

// setWrapped implements the txnInterceptor interface.
func (tv *txnVerifier) setWrapped(wrapped lockedSender) {
	tv.wrapped = wrapped
}

// populateLeafInputState implements the txnInterceptor interface.
func (tv *txnVerifier) populateLeafInputState(_ *roachpb.LeafTxnInputState, _ interval.Tree) {}

// initializeLeaf implements the txnInterceptor interface.
func (tv *txnVerifier) initializeLeaf(tis *roachpb.LeafTxnInputState) {
	// Build the readsTree from the spans provided by the LeafTxnInputState, if
	// any.
	if tis != nil && tis.AllowedReadSpans != nil {
		tv.readsTree = interval.NewTree(interval.ExclusiveOverlapper)
		for _, span := range tis.AllowedReadSpans {
			if err := tv.readsTree.Insert(roachpb.MakeIntervalSpan(span), true /* fast */); err != nil {
				log.Fatalf(context.TODO(), "failed to initialized readsTree: %v", err)
			}
		}
		tv.readsTree.AdjustRanges()
	}
}

// populateLeafFinalState implements the txnInterceptor interface.
func (tv *txnVerifier) populateLeafFinalState(_ *roachpb.LeafTxnFinalState) {}

// importLeafFinalState implements the txnInterceptor interface.
func (tv *txnVerifier) importLeafFinalState(_ context.Context, _ *roachpb.LeafTxnFinalState) error {
	return nil
}

// epochBumpedLocked implements the txnInterceptor interface.
func (tv *txnVerifier) epochBumpedLocked() {}

// createSavepointLocked implements the txnInterceptor interface.
func (tv *txnVerifier) createSavepointLocked(_ context.Context, _ *savepoint) {}

// rollbackToSavepointLocked implements the txnInterceptor interface.
func (tv *txnVerifier) rollbackToSavepointLocked(_ context.Context, _ savepoint) {}

// releaseSavepointLocked implements the txnInterceptor interface.
func (tv *txnVerifier) releaseSavepointLocked(_ context.Context, _ *savepoint) {}

// closeLocked implements the txnInterceptor interface.
func (tv *txnVerifier) closeLocked() {
	// Clean up verification state.
	tv.readsTree = nil
}
