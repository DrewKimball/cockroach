# Per-Node KV Batch Requests - Implementation Status

## Completed

### Phase 1: Protobuf Definitions ✅
**Files Modified:**
- `pkg/kv/kvpb/api.proto` (lines 3021-3029, 3144-3175, 3801-3803)

**Changes:**
- Added `NodeBatchRequest` message with `batches`, `gateway_node_id`, and `profile_labels` fields
- Added `NodeBatchResponse` message with `responses` and `now` fields
- Added `PerNodeBatchingEnabled` bool field to `BatchRequest.Header` (field 39)
- Added `NodeBatch` RPC method to `Internal` service
- Generated protobuf code successfully via `./dev generate protobuf`

### Phase 2: Server-Side Handler ✅
**Files Modified:**
- `pkg/server/node.go` (lines 188-218, 259-261, 283-285, 1889-1968)

**Changes:**
- Added metrics metadata: `metaNodeBatchCount` and `metaNodeBatchRangeCount`
- Updated `nodeMetrics` struct with `NodeBatchCount` and `NodeBatchRangeCount` counters
- Implemented `Node.NodeBatch()` handler (lines 1892-1948):
  - Updates metrics
  - Sets up context and tenant ID
  - Applies profiler labels if configured
  - Validates all range descriptors upfront via `validateNodeBatchDescriptors()`
  - Processes each batch sequentially using existing `batchInternal()` logic
  - Propagates gateway node ID to batches
  - Returns `NodeBatchResponse` with clock timestamp
- Implemented `validateNodeBatchDescriptors()` (lines 1950-1965):
  - Checks that RangeID is set for each batch
  - Verifies replica exists on this node
  - Detailed validation deferred to `batchInternal()` -> `stores.SendWithWriteBytes()`

**Design Decisions:**
- Sequential processing initially (parallel can be added later)
- Upfront validation catches missing ranges early
- Detailed descriptor/lease validation happens in existing `batchInternal()` path
- Metrics track both node batch count and total range batches processed

### Phase 3: Client-Side DistSender Infrastructure ✅
**Files Modified:**
- `pkg/kv/kvclient/kvcoord/dist_sender.go` (lines 3378-3405)

**Changes:**
- Added `rangeBatchInfo` struct to bundle batch info for per-node grouping:
  ```go
  type rangeBatchInfo struct {
      ba        *kvpb.BatchRequest
      rs        roachpb.RSpan
      positions []int
      token     rangecache.EvictionToken
      nodeID    roachpb.NodeID
  }
  ```
- Added `sendNodeBatch()` stub function with TODO comments
  - Documented need for nodedialer access (currently encapsulated in Transport)
  - Returns error for now - requires transport integration

**Transport Integration Challenge:**
The DistSender doesn't have direct access to `nodedialer.Dialer` - it's encapsulated within the Transport layer. Three options to proceed:

1. **Add nodeDialer to DistSender** (cleanest):
   - Pass via `DistSenderConfig`
   - DistSender creates connections directly for NodeBatch
   - Minimal changes to existing code

2. **Extend Transport interface**:
   - Add `SendNodeBatch()` method
   - Implement in `grpcTransport`
   - More invasive but keeps connection logic in Transport

3. **Internal Transport handling**:
   - Transport detects when multiple batches go to same node
   - Automatically uses NodeBatch RPC
   - Most transparent but requires Transport refactoring

**Recommended: Option 1** - Add nodeDialer field to DistSender for direct NodeBatch RPC calls.

## Remaining Work

### Phase 3: Complete DistSender Integration 🚧

**1. Add nodedialer to DistSender:**
```go
// In DistSender struct (line ~743):
nodeDialer *nodedialer.Dialer

// In DistSenderConfig (line ~808):
NodeDialer *nodedialer.Dialer

// In NewDistSender (line ~895):
ds.nodeDialer = cfg.NodeDialer
```

**2. Implement sendNodeBatch():**
```go
func (ds *DistSender) sendNodeBatch(...) (*kvpb.NodeBatchResponse, error) {
    req := &kvpb.NodeBatchRequest{...}
    for i, rb := range batches {
        req.Batches[i] = *rb.ba
    }
    conn, err := ds.nodeDialer.Dial(ctx, nodeID, rpcbase.DefaultClass)
    if err != nil {
        return nil, err
    }
    client := kvpb.NewInternalClient(conn)
    return client.NodeBatch(ctx, req)
}
```

**3. Add sendGroupedByNode():**
- Group `rangeBatchInfo` by `nodeID`
- For single-range groups: use existing `sendPartialBatch()`
- For multi-range groups: call `sendNodeBatch()`, combine responses
- Handle errors: fallback to individual sends on RPC failure
- Handle stale descriptors from upfront validation

**4. Modify divideAndSendBatchToRanges():**
- After line 1821 (single-range fast path): add single-node check
- In range iteration loop: collect `rangeBatchInfo` objects
- Before response channel processing: check `PerNodeBatchingEnabled`
- If enabled: call `sendGroupedByNode()` instead of individual sends

**5. Add helper functions:**
- `checkSingleNode()`: scan ranges to see if all on one node
- `sendSingleNodeBatch()`: fast path for single-node multi-range batches

### Phase 4: Streamer Integration ⏸️
- Rename `singleRangeBatch` to `partitionedBatch`
- Partition by node when `PerNodeBatchingEnabled` is set
- Handle OutOfOrder vs InOrder result ordering
- Memory accounting unchanged

### Phase 5: Testing ⏸️
- Unit tests for NodeBatch RPC
- DistSender integration tests
- Streamer tests with per-node batching
- Performance benchmarks

## Build Status

✅ All code compiles successfully:
- `./dev build ./pkg/server/node.go` - Success
- `./dev build ./pkg/kv/kvclient/kvcoord` - Success
- `./dev generate protobuf` - Success

## Critical Files Modified

| File | Lines Modified | Status |
|------|----------------|--------|
| `pkg/kv/kvpb/api.proto` | 3021-3029, 3144-3175, 3801-3803 | ✅ Complete |
| `pkg/kv/kvpb/api.pb.go` | Generated | ✅ Complete |
| `pkg/server/node.go` | 188-218, 259-261, 283-285, 1889-1968 | ✅ Complete |
| `pkg/kv/kvclient/kvcoord/dist_sender.go` | 3378-3405 | 🚧 Infrastructure added, integration pending |

## Testing Strategy

Once DistSender integration is complete:

1. **Unit Tests:**
   - `TestNodeBatchHandler`: verify server processes multiple batches
   - `TestNodeBatchValidation`: verify upfront descriptor checks
   - `TestNodeBatchMetrics`: verify counters increment correctly
   - `TestDistSenderNodeBatching`: verify client groups by node
   - `TestDistSenderNodeBatchingFallback`: verify error handling

2. **Integration Tests:**
   - Multi-range table spanning one node
   - Mixed single/multi-node batches
   - Stale descriptor handling
   - RPC failures and retries

3. **Performance:**
   - Benchmark RPC count reduction
   - Measure latency impact
   - Stress test with many ranges

## Next Steps

1. Add `nodeDialer` field to `DistSender` and `DistSenderConfig`
2. Complete `sendNodeBatch()` implementation
3. Implement `sendGroupedByNode()` with error handling
4. Integrate into `divideAndSendBatchToRanges()`
5. Add comprehensive unit tests
6. Performance validation
7. Consider Streamer integration for maximum benefit
