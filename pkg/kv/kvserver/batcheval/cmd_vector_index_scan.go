// Copyright 2024 The Cockroach Authors.
//
// Use of this software is governed by the CockroachDB Software License
// included in the /LICENSE file.

package batcheval

import (
	"context"
	"time"

	"github.com/cockroachdb/cockroach/pkg/kv/kvpb"
	"github.com/cockroachdb/cockroach/pkg/kv/kvserver/batcheval/result"
	"github.com/cockroachdb/cockroach/pkg/roachpb"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/cspann"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/cspann/quantize"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/cspann/workspace"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/vecencoding"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/vecstore"
	"github.com/cockroachdb/cockroach/pkg/storage"
	"github.com/cockroachdb/cockroach/pkg/util/encoding"
	"github.com/cockroachdb/errors"
)

func init() {
	RegisterReadWriteCommand(kvpb.VectorIndexScan, DefaultDeclareIsolatedKeys, VectorIndexScan)
}

func VectorIndexScan(
	ctx context.Context, readWriter storage.ReadWriter, cArgs CommandArgs, resp kvpb.Response,
) (result.Result, error) {
	args := cArgs.Args.(*kvpb.VectorIndexScanRequest)
	h := cArgs.Header
	reply := resp.(*kvpb.VectorIndexScanResponse)

	readCategory := ScanReadCategory(cArgs.EvalCtx.AdmissionHeader())
	opts := storage.MVCCScanOptions{
		Inconsistent:            h.ReadConsistency != kvpb.CONSISTENT,
		Txn:                     h.Txn,
		ScanStats:               cArgs.ScanStats,
		Uncertainty:             cArgs.Uncertainty,
		MaxKeys:                 h.MaxSpanRequestKeys,
		MaxLockConflicts:        storage.MaxConflictsPerLockConflictError.Get(&cArgs.EvalCtx.ClusterSettings().SV),
		TargetLockConflictBytes: storage.TargetBytesPerLockConflictError.Get(&cArgs.EvalCtx.ClusterSettings().SV),
		TargetBytes:             h.TargetBytes,
		AllowEmpty:              h.AllowEmpty,
		WholeRowsOfSize:         h.WholeRowsOfSize,
		Reverse:                 false,
		MemoryAccount:           cArgs.EvalCtx.GetResponseMemoryAccount(),
		DontInterleaveIntents:   cArgs.DontInterleaveIntents,
		ReadCategory:            readCategory,
	}

	getEncodedVal := func(rawBytes []byte) ([]byte, error) {
		mvccVal, err := storage.DecodeMVCCValue(rawBytes)
		if err != nil {
			return nil, err
		}
		return mvccVal.Value.GetBytes()
	}

	// TODO(drewk,mw5h): We could push the distance calculation logic deeper and
	// avoid materializing the KVs in intermediate buffers. E.g., we could
	// implement the results interface.
	scanRes, err := storage.MVCCScan(ctx, readWriter, args.Key, args.EndKey, h.Timestamp, opts)
	if err != nil {
		return result.Result{}, err
	}
	if len(scanRes.KVs) == 0 {
		// Partition not found. Return a response with Level=0 (InvalidLevel)
		// rather than an error, so that the caller can handle this per-partition
		// without failing the entire batch.
		var res result.Result
		res.Local.EncounteredIntents = scanRes.Intents
		return res, nil
	}
	reply.NumKeys = scanRes.NumKeys
	reply.NumBytes = scanRes.NumBytes

	// The metadata row is always the first entry in the partition's KV span.
	metadataKey := scanRes.KVs[0].Key
	metadataVal, err := getEncodedVal(scanRes.KVs[0].Value.RawBytes)
	if err != nil {
		return result.Result{}, err
	}
	md, err := vecencoding.DecodeMetadataValue(metadataVal)
	if err != nil {
		return result.Result{}, err
	}

	// Populate partition metadata in the response.
	reply.Level = uint32(md.Level)
	reply.State = uint32(md.StateDetails.State)
	reply.Target1 = uint64(md.StateDetails.Target1)
	reply.Target2 = uint64(md.StateDetails.Target2)
	reply.Source = uint64(md.StateDetails.Source)
	reply.StateTimestamp = md.StateDetails.Timestamp.UnixNano()

	// Filter out leaf vectors if requested.
	vectorKVs := scanRes.KVs[1:]
	if args.ExcludeLeafVectors && md.Level == cspann.LeafLevel {
		vectorKVs = nil
	}

	numVectors := len(vectorKVs)
	reply.Count = uint64(numVectors)

	if numVectors == 0 {
		var res result.Result
		res.Local.EncounteredIntents = scanRes.Intents
		return res, nil
	}

	// The key for each vector is prefixed by the partition key, followed by the
	// child key.
	prefixLen := vecencoding.EncodedPrefixVectorKeyLen(metadataKey, md.Level)
	switch md.Level {
	case cspann.InvalidLevel:
		return result.Result{}, errors.AssertionFailedf("vector index level cannot be zero")
	case cspann.LeafLevel:
		// At the leaf level, index entries point to the primary key.
		reply.ChildPrimaryKeys = make([]roachpb.Key, numVectors)
		for i := range vectorKVs {
			reply.ChildPrimaryKeys[i] = vectorKVs[i].Key[prefixLen:]
		}
	default:
		// At non-leaf levels, index entries point to the next level.
		reply.ChildPartitionKeys = make([]uint64, numVectors)
		for i := range vectorKVs {
			_, childPartitionKey, err := encoding.DecodeUvarintAscending(vectorKVs[i].Key[prefixLen:])
			if err != nil {
				return result.Result{}, err
			}
			reply.ChildPartitionKeys[i] = childPartitionKey
		}
	}

	var quantizer quantize.Quantizer
	reply.SquaredDistances = make([]float32, numVectors)
	reply.ErrorBounds = make([]float32, numVectors)
	switch cspann.PartitionKey(args.PartitionKey) {
	case cspann.InvalidKey:
		return result.Result{}, errors.AssertionFailedf("invalid partition key in vector index scan")
	case cspann.RootKey:
		// The root partition does not quantize vectors.
		quantizer = quantize.NewUnQuantizer(int(args.Dims), args.Metric)
	default:
		quantizer = quantize.NewRaBitQuantizer(int(args.Dims), args.Seed, args.Metric)
	}
	// TODO(drewk,mw5h): if/when we support storing columns, there may be multiple
	// leaf entries per indexed row due to column families. For now we can assume
	// one leaf entry per row.
	//
	// TODO(drewk,mw5h): we could reuse memory by estimating the distance
	// immediately after decoding each vector, rather than after decoding all
	// vectors.
	set := quantizer.NewSet(numVectors, md.Centroid)
	reply.ValueBytes = make([][]byte, numVectors)
	for i := range vectorKVs {
		encVal, err := getEncodedVal(vectorKVs[i].Value.RawBytes)
		if err != nil {
			return result.Result{}, err
		}
		remainder, err := vecstore.DecodeVectorToSet(quantizer, set, encVal)
		if err != nil {
			return result.Result{}, err
		}
		if len(remainder) > 0 {
			reply.ValueBytes[i] = remainder
		}
	}
	var w workspace.T
	quantizer.EstimateDistances(&w, set, args.QueryVector, reply.SquaredDistances, reply.ErrorBounds)

	var res result.Result
	res.Local.EncounteredIntents = scanRes.Intents
	return res, nil
}

// DecodeVectorIndexScanResponseTimestamp decodes the state timestamp from a
// VectorIndexScanResponse into a time.Time.
func DecodeVectorIndexScanResponseTimestamp(nanos int64) time.Time {
	if nanos == 0 {
		return time.Time{}
	}
	return time.Unix(0, nanos).UTC()
}
