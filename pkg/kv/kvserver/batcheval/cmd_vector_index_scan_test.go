// Copyright 2024 The Cockroach Authors.
//
// Use of this software is governed by the CockroachDB Software License
// included in the /LICENSE file.

package batcheval

import (
	"context"
	"fmt"
	"math/rand"
	"strings"
	"testing"

	"github.com/cockroachdb/cockroach/pkg/kv/kvpb"
	"github.com/cockroachdb/cockroach/pkg/roachpb"
	"github.com/cockroachdb/cockroach/pkg/settings/cluster"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/cspann"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/cspann/quantize"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/cspann/testutils"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/cspann/workspace"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/vecencoding"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/vecpb"
	"github.com/cockroachdb/cockroach/pkg/storage"
	"github.com/cockroachdb/cockroach/pkg/util/encoding"
	"github.com/cockroachdb/cockroach/pkg/util/hlc"
	"github.com/cockroachdb/cockroach/pkg/util/leaktest"
	"github.com/cockroachdb/cockroach/pkg/util/log"
	"github.com/cockroachdb/cockroach/pkg/util/num32"
	"github.com/cockroachdb/cockroach/pkg/util/randutil"
	"github.com/cockroachdb/cockroach/pkg/util/vector"
	"github.com/stretchr/testify/require"
)

func TestVectorIndexScan(t *testing.T) {
	defer leaktest.AfterTest(t)()
	defer log.Scope(t).Close(t)

	ctx := context.Background()
	settings := cluster.MakeTestingClusterSettings()
	eng := storage.NewDefaultInMemForTesting()
	defer eng.Close()

	rnd, seed := randutil.NewTestRand()
	t.Logf("random seed: %v", seed)
	var tsCounter int64
	ts := func() hlc.Timestamp {
		tsCounter++
		return hlc.Timestamp{WallTime: tsCounter}
	}
	var testID int
	dims := rnd.Intn(100) + 1
	set := testutils.RandomVectorSet(rnd, dims)
	indexSeed := rnd.Int63()
	for _, metric := range []vecpb.DistanceMetric{
		vecpb.L2SquaredDistance,
		vecpb.InnerProductDistance,
		vecpb.CosineDistance,
	} {
		t.Run(metric.String(), func(t *testing.T) {
			// Cosine distance requires unit vectors.
			metricSet := set
			if metric == vecpb.CosineDistance {
				metricSet = vector.MakeSet(dims)
				metricSet.AddSet(set)
				for i := range metricSet.Count {
					num32.Normalize(metricSet.At(i))
				}
			}
			centroid := metricSet.Centroid(make(vector.T, dims))
			for _, quantizer := range []quantize.Quantizer{
				quantize.NewUnQuantizer(dims, metric),
				quantize.NewRaBitQuantizer(dims, indexSeed, metric),
			} {
				var w workspace.T
				quantizerName := strings.TrimPrefix(fmt.Sprintf("%T", quantizer), "*quantize.")
				quantizedSet := quantizer.Quantize(&w, metricSet)
				t.Run(quantizerName, func(t *testing.T) {
					nonLeafLevel := cspann.Level(rnd.Intn(10)) + cspann.SecondLevel
					for _, level := range []cspann.Level{cspann.LeafLevel, nonLeafLevel} {
						t.Run(fmt.Sprintf("level=%d", level), func(t *testing.T) {
							// The handler picks the quantizer based on the partition
							// key: RootKey uses UnQuantizer, all others use
							// RaBitQuantizer. Match the partition key to the quantizer.
							var partitionKey cspann.PartitionKey
							switch quantizer.(type) {
							case *quantize.UnQuantizer:
								partitionKey = cspann.RootKey
							default:
								partitionKey = cspann.PartitionKey(randutil.RandUint64n(rnd, 998) + 2)
							}
							// Use a unique index prefix per subtest to avoid key
							// collisions in the shared engine.
							testID++
							indexPrefix := encoding.EncodeUvarintAscending(nil, uint64(testID))
							startKey, endKey := putQuantizedVectorSet(
								t, ctx, eng, quantizedSet, centroid, level, partitionKey, indexPrefix, ts,
							)
							for range 10 {
								// Generate a random query vector and perform a vector index scan.
								queryVector := vector.Random(rnd, dims)
								if metric == vecpb.CosineDistance {
									num32.Normalize(queryVector)
								}
								req := &kvpb.VectorIndexScanRequest{
									Metric:       metric,
									PartitionKey: uint64(partitionKey),
									Dims:         uint64(dims),
									Seed:         indexSeed,
									QueryVector:  queryVector,
								}
								req.SetHeader(kvpb.RequestHeader{Key: startKey, EndKey: endKey})
								resp := &kvpb.VectorIndexScanResponse{}
								cArgs := CommandArgs{
									Args:    req,
									Header:  kvpb.Header{Timestamp: ts()},
									EvalCtx: (&MockEvalCtx{ClusterSettings: settings}).EvalContext(),
								}
								_, err := VectorIndexScan(ctx, eng, cArgs, resp)
								require.NoError(t, err)

								// Verify the response.
								squaredDistances := make([]float32, set.Count)
								errorBounds := make([]float32, set.Count)
								quantizer.EstimateDistances(
									&w, quantizedSet, queryVector, squaredDistances, errorBounds,
								)
								require.Equal(t, uint64(set.Count), resp.Count)
								require.Equal(t, squaredDistances, resp.SquaredDistances)
								require.Equal(t, errorBounds, resp.ErrorBounds)
								require.Equal(t, uint32(level), resp.Level)
								if level == cspann.LeafLevel {
									require.Zero(t, len(resp.ChildPartitionKeys))
									require.Equal(t, set.Count, len(resp.ChildPrimaryKeys))
									for i := range set.Count {
										require.Equal(t, roachpb.Key(getEncPrimaryKey(i)), resp.ChildPrimaryKeys[i])
									}
								} else {
									require.Zero(t, len(resp.ChildPrimaryKeys))
									require.Equal(t, set.Count, len(resp.ChildPartitionKeys))
									for i := range set.Count {
										require.Equal(t, uint64(i), resp.ChildPartitionKeys[i])
									}
								}
							}
						})
					}
				})
			}
		})
	}
}

// putQuantizedVectorSet encodes the given quantized vector set and writes it to
// the engine. It returns the start and end keys for scanning the partition.
//
// The key suffix and child key for each vector is the index of the vector
// within the partition.
func putQuantizedVectorSet(
	t *testing.T,
	ctx context.Context,
	eng storage.Engine,
	set quantize.QuantizedVectorSet,
	centroid vector.T,
	level cspann.Level,
	partitionKey cspann.PartitionKey,
	indexPrefix roachpb.Key,
	ts func() hlc.Timestamp,
) (startKey, endKey roachpb.Key) {
	mdKey := vecencoding.EncodeMetadataKey(
		indexPrefix, nil /* encodedPrefixCols */, partitionKey,
	)

	// Build vector key prefix from the metadata key and level.
	vectorKeyPrefix := vecencoding.EncodePrefixVectorKey(mdKey, level)
	vectorKey := func(i int) roachpb.Key {
		var childKey cspann.ChildKey
		if level == cspann.LeafLevel {
			childKey.KeyBytes = getEncPrimaryKey(i)
		} else {
			childKey.PartitionKey = cspann.PartitionKey(i)
		}
		return vecencoding.EncodeChildKey(vectorKeyPrefix, childKey)
	}

	metadata := cspann.PartitionMetadata{Level: level, Centroid: centroid}
	metadata.StateDetails.MakeReady()
	mdVal := vecencoding.EncodeMetadataValue(metadata)
	_, err := storage.MVCCPut(
		ctx, eng, mdKey, ts(), roachpb.MakeValueFromBytes(mdVal),
		storage.MVCCWriteOptions{},
	)
	require.NoError(t, err)
	for i := 0; i < set.GetCount(); i++ {
		var encVector []byte
		switch quantizedSet := set.(type) {
		case *quantize.UnQuantizedVectorSet:
			encVector = vecencoding.EncodeUnquantizerVector(encVector, quantizedSet.Vectors.At(i))
		case *quantize.RaBitQuantizedVectorSet:
			encVector = vecencoding.EncodeRaBitQVectorFromSet(encVector, quantizedSet, i)
		}
		_, err = storage.MVCCPut(
			ctx, eng, vectorKey(i), ts(), roachpb.MakeValueFromBytes(encVector),
			storage.MVCCWriteOptions{},
		)
		require.NoError(t, err)
	}

	startKey = mdKey
	endKey = vecencoding.EncodeEndVectorKey(mdKey)
	return startKey, endKey
}

func getEncPrimaryKey(i int) []byte {
	pk := encoding.EncodeUint64Ascending(nil, uint64(i))
	rnd := rand.New(rand.NewSource(int64(i)))
	return encoding.EncodeBytesAscending(pk, randutil.RandBytes(rnd, 16))
}
