// Copyright 2026 The Cockroach Authors.
//
// Use of this software is governed by the CockroachDB Software License
// included in the /LICENSE file.

package storage

import (
	"context"
	"fmt"
	"testing"

	"github.com/cockroachdb/cockroach/pkg/keys"
	"github.com/cockroachdb/cockroach/pkg/kv/kvserver/concurrency/lock"
	"github.com/cockroachdb/cockroach/pkg/kv/kvserver/uncertainty"
	"github.com/cockroachdb/cockroach/pkg/roachpb"
	"github.com/cockroachdb/cockroach/pkg/storage/enginepb"
	"github.com/cockroachdb/cockroach/pkg/util/encoding"
	"github.com/cockroachdb/cockroach/pkg/util/hlc"
	"github.com/cockroachdb/cockroach/pkg/util/leaktest"
	"github.com/cockroachdb/cockroach/pkg/util/mon"
	"github.com/cockroachdb/cockroach/pkg/util/protoutil"
	"github.com/cockroachdb/cockroach/pkg/util/uuid"
	"github.com/stretchr/testify/require"
)

// TestMVCCScanSkipLockedMultiColumnFamily tests that SKIP LOCKED correctly
// handles tables with multiple column families by skipping entire rows when
// any KV in the row is locked. Tests all possible combinations of:
// - Lock positions (every possible subset of families)
// - Number of column families (1 through 5)
// - Lock types (replicated intents and unreplicated locks)
func TestMVCCScanSkipLockedMultiColumnFamily(t *testing.T) {
	defer leaktest.AfterTest(t)()

	makeTableKey := func(pk int, familyID uint32) roachpb.Key {
		codec := keys.SystemSQLCodec
		tableKey := codec.IndexPrefix(50, 1)
		tableKey = encoding.EncodeVarintAscending(tableKey, int64(pk))
		tableKey = keys.MakeFamilyKey(tableKey, familyID)
		return roachpb.Key(tableKey)
	}

	// runTest is the helper function that runs a single test case.
	runTest := func(t *testing.T, lockType string, numFamilies int, lockedFamilyIDs []uint32) {
		eng := createTestPebbleEngine()
		defer eng.Close()

		ctx := context.Background()
		ts := hlc.Timestamp{WallTime: 1}

		// Create 3 rows, each with numFamilies column families.
		var allKeys []roachpb.Key
		for pk := 1; pk <= 3; pk++ {
			for familyID := uint32(0); familyID < uint32(numFamilies); familyID++ {
				allKeys = append(allKeys, makeTableKey(pk, familyID))
			}
		}

		// Insert all KVs.
		for _, k := range allKeys {
			mvccKey := MVCCKey{Key: k, Timestamp: ts}
			value := MVCCValue{Value: roachpb.MakeValueFromString("value")}
			require.NoError(t, eng.PutMVCC(mvccKey, value))
		}

		// Define the scan bounds for the test.
		codec := keys.SystemSQLCodec
		startKey := codec.IndexPrefix(50, 1)
		endKey := codec.IndexPrefix(50, 2)

		// Create locks on row 2 at the specified families.
		txnID := uuid.MakeV4()
		txnMeta := &enginepb.TxnMeta{
			ID:             txnID,
			WriteTimestamp: ts,
		}

		var lockTable *mockLockTableView

		if lockType == "replicated" {
			// Write intents at all the locked keys.
			lockTable = &mockLockTableView{
				unreplLocks: map[string]unreplicatedLockInfo{},
				txn:         nil,
				ts:          hlc.Timestamp{WallTime: 1},
				str:         lock.None,
			}

			for _, lockedFamilyID := range lockedFamilyIDs {
				lockedKey := makeTableKey(2, lockedFamilyID)
				meta := &enginepb.MVCCMetadata{
					Txn:       txnMeta,
					Timestamp: hlc.LegacyTimestamp(txnMeta.WriteTimestamp),
					KeyBytes:  2,
					ValBytes:  2,
				}
				metaBytes, err := protoutil.Marshal(meta)
				require.NoError(t, err)

				lockTableKey, _ := LockTableKey{
					Key:      lockedKey,
					Strength: lock.Intent,
					TxnUUID:  txnMeta.ID,
				}.ToEngineKey(nil)
				require.NoError(t, eng.PutEngineKey(lockTableKey, metaBytes))
			}
		} else {
			// Use unreplicated locks.
			unreplLocks := make(map[string]unreplicatedLockInfo)
			for _, lockedFamilyID := range lockedFamilyIDs {
				lockedKey := makeTableKey(2, lockedFamilyID)
				unreplLocks[string(lockedKey)] = unreplicatedLockInfo{
					txn: txnMeta,
					str: lock.Exclusive,
				}
			}
			lockTable = &mockLockTableView{
				unreplLocks: unreplLocks,
				txn:         nil,
				ts:          hlc.Timestamp{WallTime: 1},
				str:         lock.None,
			}
		}

		// Perform a SKIP LOCKED scan.
		reader := eng.NewReader(StandardDurability)
		defer reader.Close()

		iter, err := reader.NewMVCCIterator(ctx, MVCCKeyAndIntentsIterKind, IterOptions{
			LowerBound: startKey,
			UpperBound: endKey,
		})
		require.NoError(t, err)
		defer iter.Close()

		var results pebbleResults
		results.lastOffsetsEnabled = true
		// Use 2x row size to track at least 2 complete rows, matching production code.
		results.lastOffsets = make([]int, 2*numFamilies)

		mvccScanner := pebbleMVCCScanner{
			parent:     iter,
			memAccount: mon.NewStandaloneUnlimitedAccount(),
			lockTable:  lockTable,
			reverse:    false,
			start:      startKey,
			end:        endKey,
			ts:         ts,
			skipLocked: true,
			wholeRows:  true,
		}

		mvccScanner.init(nil, uncertainty.Interval{}, &results)
		mvccScanner.skipLockedMultiFamily.enabled = true
		mvccScanner.skipLockedMultiFamily.currentRowPrefix = make([]byte, 0, 64)

		_, _, _, err = mvccScanner.scan(ctx)
		require.NoError(t, err)

		// Verify results: should only have rows 1 and 3 (row 2 should be skipped).
		kvData := results.finish()
		numKeys := results.count

		// Decode the keys to see what we actually got.
		var scannedKeys []roachpb.Key
		require.NoError(t, MVCCScanDecodeKeyValues(kvData, func(k MVCCKey, v []byte) error {
			scannedKeys = append(scannedKeys, k.Key)
			return nil
		}))

		// Expected keys: row 1 and row 3, all families.
		var expectedKeys []roachpb.Key
		for pk := 1; pk <= 3; pk++ {
			if pk == 2 {
				continue // Row 2 is locked and should be skipped
			}
			for familyID := uint32(0); familyID < uint32(numFamilies); familyID++ {
				expectedKeys = append(expectedKeys, makeTableKey(pk, familyID))
			}
		}

		require.Equal(t, len(expectedKeys), len(scannedKeys),
			"Row 2 should be completely skipped, got %d keys, want %d keys\nScanned: %v\nExpected: %v",
			len(scannedKeys), len(expectedKeys), scannedKeys, expectedKeys)

		expectedCount := int64(2 * numFamilies) // 2 rows × numFamilies
		require.Equal(t, expectedCount, numKeys,
			fmt.Sprintf("Expected %d KVs (2 rows × %d families)", expectedCount, numFamilies))

		for i, expectedKey := range expectedKeys {
			require.Equal(t, expectedKey, scannedKeys[i],
				"Key mismatch at position %d", i)
		}
	}

	// Helper function to generate all non-empty subsets of [0, 1, ..., n-1].
	// Uses bit manipulation: for n items, iterate from 1 to 2^n - 1.
	generateSubsets := func(n int) [][]uint32 {
		var subsets [][]uint32
		numSubsets := (1 << n) - 1 // 2^n - 1 (exclude empty set)
		for i := 1; i <= numSubsets; i++ {
			var subset []uint32
			for bit := 0; bit < n; bit++ {
				if i&(1<<bit) != 0 {
					subset = append(subset, uint32(bit))
				}
			}
			subsets = append(subsets, subset)
		}
		return subsets
	}

	// Test all combinations of lock types, number of families, and locked family subsets.
	for _, lockType := range []string{"unreplicated", "replicated"} {
		t.Run(lockType, func(t *testing.T) {
			for numFamilies := 1; numFamilies <= 7; numFamilies++ {
				t.Run(fmt.Sprintf("%d families", numFamilies), func(t *testing.T) {
					subsets := generateSubsets(numFamilies)
					for _, lockedFamilyIDs := range subsets {
						// Build a descriptive test name.
						testName := "lock families"
						for i, familyID := range lockedFamilyIDs {
							if i == 0 {
								testName = fmt.Sprintf("%s %d", testName, familyID)
							} else {
								testName = fmt.Sprintf("%s,%d", testName, familyID)
							}
						}
						t.Run(testName, func(t *testing.T) {
							runTest(t, lockType, numFamilies, lockedFamilyIDs)
						})
					}
				})
			}
		})
	}
}

// mockLockTableView is a simple mock implementation of LockTableView for testing.
type mockLockTableView struct {
	unreplLocks map[string]unreplicatedLockInfo
	txn         *roachpb.Transaction
	ts          hlc.Timestamp
	str         lock.Strength
}

type unreplicatedLockInfo struct {
	txn *enginepb.TxnMeta
	str lock.Strength
}

func (lt *mockLockTableView) IsKeyLockedByConflictingTxn(
	_ context.Context, k roachpb.Key,
) (bool, *enginepb.TxnMeta, error) {
	info, ok := lt.unreplLocks[string(k)]
	if !ok {
		return false, nil, nil
	}
	holder := info.txn
	if lt.txn != nil && lt.txn.ID == holder.ID {
		return false, nil, nil
	}
	return true, holder, nil
}

func (lt *mockLockTableView) Close() {}

// TestPebbleResultsTruncateTo tests the truncateTo method which removes KVs
// from the end of the results back to a target count.
func TestPebbleResultsTruncateTo(t *testing.T) {
	defer leaktest.AfterTest(t)()

	ctx := context.Background()
	memAccount := mon.NewStandaloneUnlimitedAccount()

	// Helper to create a test key-value pair.
	makeKV := func(key string, value string) ([]byte, []byte) {
		mvccKey := MVCCKey{Key: roachpb.Key(key), Timestamp: hlc.Timestamp{WallTime: 1}}
		encoded := EncodeMVCCKey(mvccKey)
		return encoded, []byte(value)
	}

	t.Run("truncate to zero", func(t *testing.T) {
		var p pebbleResults
		p.lastOffsetsEnabled = true
		p.lastOffsets = make([]int, 5)

		// Add 3 KVs.
		for i := 0; i < 3; i++ {
			key, val := makeKV(fmt.Sprintf("key%d", i), fmt.Sprintf("value%d", i))
			require.NoError(t, p.put(ctx, key, val, memAccount, 0))
		}

		require.Equal(t, int64(3), p.count)
		initialBytes := p.bytes

		// Truncate to 0.
		p.truncateTo(0)

		require.Equal(t, int64(0), p.count)
		require.Equal(t, int64(0), p.bytes)
		require.Equal(t, 0, len(p.repr))
		require.Equal(t, 0, p.lastOffsetIdx)
		require.True(t, initialBytes > 0, "should have had bytes before truncation")
	})

	t.Run("truncate to partial count", func(t *testing.T) {
		var p pebbleResults
		p.lastOffsetsEnabled = true
		p.lastOffsets = make([]int, 5)

		// Add 5 KVs.
		for i := 0; i < 5; i++ {
			key, val := makeKV(fmt.Sprintf("key%d", i), fmt.Sprintf("value%d", i))
			require.NoError(t, p.put(ctx, key, val, memAccount, 0))
		}

		require.Equal(t, int64(5), p.count)
		bytesAfter3 := int64(0)

		// Snapshot bytes after first 3 KVs by calculating.
		var p2 pebbleResults
		p2.lastOffsetsEnabled = true
		p2.lastOffsets = make([]int, 5)
		for i := 0; i < 3; i++ {
			key, val := makeKV(fmt.Sprintf("key%d", i), fmt.Sprintf("value%d", i))
			require.NoError(t, p2.put(ctx, key, val, memAccount, 0))
		}
		bytesAfter3 = p2.bytes

		// Truncate to 3.
		p.truncateTo(3)

		require.Equal(t, int64(3), p.count)
		require.Equal(t, bytesAfter3, p.bytes)
	})

	t.Run("truncate no-op when target >= count", func(t *testing.T) {
		var p pebbleResults
		p.lastOffsetsEnabled = true
		p.lastOffsets = make([]int, 5)

		// Add 3 KVs.
		for i := 0; i < 3; i++ {
			key, val := makeKV(fmt.Sprintf("key%d", i), fmt.Sprintf("value%d", i))
			require.NoError(t, p.put(ctx, key, val, memAccount, 0))
		}

		initialCount := p.count
		initialBytes := p.bytes

		// Truncate to same count - should be no-op.
		p.truncateTo(3)
		require.Equal(t, initialCount, p.count)
		require.Equal(t, initialBytes, p.bytes)

		// Truncate to higher count - should be no-op.
		p.truncateTo(5)
		require.Equal(t, initialCount, p.count)
		require.Equal(t, initialBytes, p.bytes)
	})

	t.Run("truncate with negative target", func(t *testing.T) {
		var p pebbleResults
		p.lastOffsetsEnabled = true
		p.lastOffsets = make([]int, 5)

		// Add 3 KVs.
		for i := 0; i < 3; i++ {
			key, val := makeKV(fmt.Sprintf("key%d", i), fmt.Sprintf("value%d", i))
			require.NoError(t, p.put(ctx, key, val, memAccount, 0))
		}

		// Truncate to negative count - should truncate to 0.
		p.truncateTo(-1)
		require.Equal(t, int64(0), p.count)
		require.Equal(t, int64(0), p.bytes)
	})

	t.Run("truncate across buffer boundaries", func(t *testing.T) {
		var p pebbleResults
		p.lastOffsetsEnabled = true
		p.lastOffsets = make([]int, 100)

		// Add enough KVs to trigger multiple buffers.
		// Each KV is roughly 20 bytes, so we need ~800 to fill a 16-byte initial buffer
		// and cause buffer rotation.
		for i := 0; i < 100; i++ {
			key, val := makeKV(fmt.Sprintf("key%d", i), fmt.Sprintf("value%d", i))
			require.NoError(t, p.put(ctx, key, val, memAccount, 0))
		}

		require.Equal(t, int64(100), p.count)
		numBufs := len(p.bufs)
		require.True(t, numBufs > 0, "should have created multiple buffers")

		// Truncate to a count that requires popping buffers.
		// The ring buffer tracks the last 100 KVs, so we can truncate to 5.
		p.truncateTo(5)

		require.Equal(t, int64(5), p.count)
		require.True(t, p.bytes > 0)
		// Should have fewer buffers now (or all in repr).
		require.True(t, len(p.bufs) < numBufs || len(p.repr) > 0)
	})
}

// TestSkipLockedMultiFamilyState tests the skipLockedMultiFamilyState helper
// struct and its methods.
func TestSkipLockedMultiFamilyState(t *testing.T) {
	defer leaktest.AfterTest(t)()

	ctx := context.Background()
	memAccount := mon.NewStandaloneUnlimitedAccount()

	// Helper to create a table key with a given row prefix and family ID.
	makeTableKey := func(pk int, familyID uint32) roachpb.Key {
		codec := keys.SystemSQLCodec
		tableKey := codec.IndexPrefix(50, 1)
		tableKey = encoding.EncodeVarintAscending(tableKey, int64(pk))
		tableKey = keys.MakeFamilyKey(tableKey, familyID)
		return tableKey
	}

	// Helper to encode a table key as an MVCC key.
	encodeMVCCKey := func(key roachpb.Key) []byte {
		mvccKey := MVCCKey{Key: key, Timestamp: hlc.Timestamp{WallTime: 1}}
		return EncodeMVCCKey(mvccKey)
	}

	t.Run("isEnabled returns enabled state", func(t *testing.T) {
		var s skipLockedMultiFamilyState
		require.False(t, s.isEnabled())

		s.enabled = true
		require.True(t, s.isEnabled())
	})

	t.Run("updateRowTracking detects new row", func(t *testing.T) {
		var results pebbleResults
		results.lastOffsetsEnabled = true
		results.lastOffsets = make([]int, 4)

		var s skipLockedMultiFamilyState
		s.enabled = true
		s.currentRowPrefix = make([]byte, 0, 64)

		// First key from row 1, family 0.
		key1f0 := makeTableKey(1, 0)
		rawKey1f0 := encodeMVCCKey(key1f0)

		// Add it to results.
		value := []byte("value")
		require.NoError(t, results.put(ctx, rawKey1f0, value, memAccount, 0))

		// Update tracking for first KV - should set row prefix.
		s.updateRowTracking(rawKey1f0, &results, true)
		require.Equal(t, int64(1), s.currentRowStartOffset)
		require.NotNil(t, s.currentRowPrefix)
		require.False(t, s.isSkipped)

		// Add second KV from same row (family 1).
		key1f1 := makeTableKey(1, 1)
		rawKey1f1 := encodeMVCCKey(key1f1)
		require.NoError(t, results.put(ctx, rawKey1f1, value, memAccount, 0))

		// Update tracking - should NOT update currentRowStartOffset (same row).
		s.updateRowTracking(rawKey1f1, &results, true)
		require.Equal(t, int64(1), s.currentRowStartOffset) // Still 1, not 2
		require.False(t, s.isSkipped)

		// Add first KV from row 2, family 0.
		key2f0 := makeTableKey(2, 0)
		rawKey2f0 := encodeMVCCKey(key2f0)
		require.NoError(t, results.put(ctx, rawKey2f0, value, memAccount, 0))

		// Update tracking - should detect new row and update offset.
		s.updateRowTracking(rawKey2f0, &results, true)
		require.Equal(t, int64(3), s.currentRowStartOffset) // New row starts at KV 3
		require.False(t, s.isSkipped)                       // resetSkipped=true
	})

	t.Run("updateRowTracking respects resetSkipped flag", func(t *testing.T) {
		var results pebbleResults
		results.lastOffsetsEnabled = true
		results.lastOffsets = make([]int, 4)

		var s skipLockedMultiFamilyState
		s.enabled = true
		s.currentRowPrefix = make([]byte, 0, 64)
		s.isSkipped = true // Start with isSkipped = true

		key1f0 := makeTableKey(1, 0)
		rawKey1f0 := encodeMVCCKey(key1f0)
		value := []byte("value")
		require.NoError(t, results.put(ctx, rawKey1f0, value, memAccount, 0))

		// Update with resetSkipped=false - should keep isSkipped=true.
		s.updateRowTracking(rawKey1f0, &results, false)
		require.True(t, s.isSkipped)

		// Now add a new row.
		key2f0 := makeTableKey(2, 0)
		rawKey2f0 := encodeMVCCKey(key2f0)
		require.NoError(t, results.put(ctx, rawKey2f0, value, memAccount, 0))

		// Update with resetSkipped=true - should clear isSkipped.
		s.updateRowTracking(rawKey2f0, &results, true)
		require.False(t, s.isSkipped)
	})

	t.Run("rollbackAndSkip truncates and marks skipped", func(t *testing.T) {
		var results pebbleResults
		results.lastOffsetsEnabled = true
		results.lastOffsets = make([]int, 4)

		var s skipLockedMultiFamilyState
		s.enabled = true
		s.currentRowPrefix = make([]byte, 0, 64)

		value := []byte("value")

		// Add 1 KV from a previous row (row 0).
		key0 := makeTableKey(0, 0)
		rawKey0 := encodeMVCCKey(key0)
		require.NoError(t, results.put(ctx, rawKey0, value, memAccount, 0))
		require.Equal(t, int64(1), results.count)

		// Start tracking a new row (row 1). In production, updateRowTracking
		// is called before adding each KV, so currentRowStartOffset captures
		// the count before the first KV of the new row is added.
		key1f0 := makeTableKey(1, 0)
		rawKey1f0 := encodeMVCCKey(key1f0)
		s.updateRowTracking(rawKey1f0, &results, true)
		require.Equal(t, int64(1), s.currentRowStartOffset)

		// Add 1 KV from row 1.
		require.NoError(t, results.put(ctx, rawKey1f0, value, memAccount, 0))
		require.Equal(t, int64(2), results.count)

		// Rollback and skip.
		s.rollbackAndSkip(&results)

		// Should have truncated back to row start, removing row 1 but keeping row 0.
		require.Equal(t, int64(1), results.count)
		require.True(t, s.isSkipped)
	})

	t.Run("shouldSkip returns isSkipped state", func(t *testing.T) {
		var s skipLockedMultiFamilyState
		require.False(t, s.shouldSkip())

		s.isSkipped = true
		require.True(t, s.shouldSkip())
	})
}
