// Copyright 2024 The Cockroach Authors.
//
// Use of this software is governed by the CockroachDB Software License
// included in the /LICENSE file.

package cspann

import (
	"context"
	"flag"
	"fmt"
	"math"
	"math/rand"
	"testing"
	"time"

	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/cspann/testutils"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/cspann/workspace"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/vecpb"
	"github.com/cockroachdb/cockroach/pkg/util/vector"
	"github.com/cockroachdb/cockroach/pkg/workload/vecann"
	"github.com/stretchr/testify/require"
)

// loadDatasetForTest loads either a small local dataset or a large downloaded dataset.
func loadDatasetForTest(t testing.TB, datasetName string) (loadedVectors vector.Set) {
	fmt.Printf("Loading dataset %q...\n", datasetName)
	start := time.Now()
	defer func() {
		duration := time.Since(start)
		fmt.Printf("Loaded %d vectors in %v\n", loadedVectors.Count, duration)
	}()

	// Map of small local datasets
	smallDatasets := map[string]string{
		"random":  testutils.RandomDataset,
		"glove":   testutils.GloveDataset,
		"fashion": testutils.FashionDataset,
		"images":  testutils.ImagesDataset,
		"laion":   testutils.LaionDataset,
		"dbpedia": testutils.DbpediaDataset,
		"clip":    testutils.ClipDataset,
	}

	// Check if it's a small local dataset
	if localDataset, isLocal := smallDatasets[datasetName]; isLocal {
		return testutils.LoadDataset(t, localDataset)
	}

	// Otherwise, assume it's a large dataset and use vecann loader
	lastDownloaded := int64(0)
	loader := vecann.DatasetLoader{
		DatasetName: datasetName,
		CacheFolder: "/tmp/crdb-test-datasets", // Use explicit cache folder for tests
		OnProgress: func(ctx context.Context, format string, args ...any) {
			fmt.Printf(format+"\n", args...)
		},
		OnDownloadProgress: func(downloaded, total int64, elapsed time.Duration) {
			// Only log after each 10% progress.
			threshold := (total + 3) / 10
			if downloaded > lastDownloaded+threshold {
				lastDownloaded = downloaded
				fmt.Printf("Downloaded %d/%d bytes (%.1f%%) in %v\n",
					downloaded, total, float64(downloaded)/float64(total)*100, elapsed)
			}
		},
	}

	if err := loader.Load(context.Background()); err != nil {
		t.Skipf("Could not load dataset %s: %v", datasetName, err)
		return vector.Set{}
	}

	// For clustering, we want to use the training data, not test data
	// Load the first batch of training data
	hasMore, err := loader.Data.Next()
	require.NoError(t, err)
	if !hasMore {
		t.Skipf("No training data available for dataset %s", datasetName)
		return vector.Set{}
	}

	return loader.Data.Train
}

func TestMiniBatchKMeans(t *testing.T) {
	workspace := &workspace.T{}
	imagesDataset := testutils.LoadDataset(t, testutils.ImagesDataset)
	imagesSubset := imagesDataset.Slice(0, 1000)

	testCases := []struct {
		desc           string
		distanceMetric vecpb.DistanceMetric
		vectors        vector.Set
		k              int
		batchSize      int
		maxIterations  int
	}{
		{
			desc:           "simple 2D vectors with L2 distance",
			distanceMetric: vecpb.L2SquaredDistance,
			vectors: vector.MakeSetFromRawData([]float32{
				1, 1,
				1.5, 1.5,
				2, 2,
				8, 8,
				8.5, 8.5,
				9, 9,
			}, 2),
			k:             2,
			batchSize:     3,
			maxIterations: 50,
		},
		{
			desc:           "3D vectors with InnerProduct distance",
			distanceMetric: vecpb.InnerProductDistance,
			vectors: vector.MakeSetFromRawData([]float32{
				1, 0, 0,
				0, 1, 0,
				0, 0, 1,
				-1, 0, 0,
				0, -1, 0,
				0, 0, -1,
			}, 3),
			k:             2,
			batchSize:     4,
			maxIterations: 50,
		},
		{
			desc:           "normalized vectors with Cosine distance",
			distanceMetric: vecpb.CosineDistance,
			vectors: vector.MakeSetFromRawData([]float32{
				1, 0, 0,
				0, 1, 0,
				0, 0, 1,
				0.7071068, 0.7071068, 0,
				0, 0.7071068, 0.7071068,
				0.7071068, 0, 0.7071068,
			}, 3),
			k:             3,
			batchSize:     2,
			maxIterations: 50,
		},
		{
			desc:           "high-dimensional vectors from images dataset",
			distanceMetric: vecpb.L2SquaredDistance,
			vectors:        imagesSubset,
			k:              10,
			batchSize:      100,
			maxIterations:  100,
		},
		{
			desc:           "fashion dataset with L2 distance",
			distanceMetric: vecpb.L2SquaredDistance,
			vectors:        testutils.LoadDataset(t, testutils.FashionDataset),
			k:              8,
			batchSize:      50,
			maxIterations:  100,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.desc, func(t *testing.T) {
			mbk := &MiniBatchKMeans{
				K:              tc.k,
				BatchSize:      tc.batchSize,
				MaxIterations:  tc.maxIterations,
				Workspace:      workspace,
				Rand:           rand.New(rand.NewSource(42)),
				DistanceMetric: tc.distanceMetric,
			}

			err := mbk.Fit(tc.vectors)
			require.NoError(t, err)

			// Verify we have the correct number of centroids
			centroids := mbk.Centroids()
			require.Equal(t, tc.k, centroids.Count)
			require.Equal(t, tc.vectors.Dims, centroids.Dims)

			// Test prediction
			assignments := make([]uint64, tc.vectors.Count)
			mbk.Predict(tc.vectors, assignments)

			// Verify all assignments are within valid range
			for _, assignment := range assignments {
				require.Less(t, assignment, uint64(tc.k))
			}

			// Calculate inertia (sum of squared distances to centroids)
			var inertia float32
			for i := range tc.vectors.Count {
				centroidIdx := assignments[i]
				distance := mbk.calculateDistance(tc.vectors.At(i), centroids.At(int(centroidIdx)))
				if tc.distanceMetric == vecpb.L2SquaredDistance {
					inertia += distance
				} else {
					inertia += distance * distance
				}
			}

			// Inertia should be reasonable (not infinite or NaN)
			require.False(t, math.IsNaN(float64(inertia)))
			require.False(t, math.IsInf(float64(inertia), 0))

			// Reset and verify state is cleared
			mbk.Reset()
			require.False(t, mbk.initialized)
		})
	}
}

func TestMiniBatchKMeansInitialization(t *testing.T) {
	workspace := &workspace.T{}
	vectors := testutils.LoadDataset(t, testutils.RandomDataset)

	testCases := []struct {
		desc       string
		initMethod InitializationMethod
	}{
		{
			desc:       "random initialization",
			initMethod: InitRandom,
		},
		{
			desc:       "k-means++ initialization",
			initMethod: InitKMeansPlusPlus,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.desc, func(t *testing.T) {
			mbk := &MiniBatchKMeans{
				K:              5,
				BatchSize:      50,
				MaxIterations:  50,
				InitMethod:     tc.initMethod,
				Workspace:      workspace,
				Rand:           rand.New(rand.NewSource(42)),
				DistanceMetric: vecpb.L2SquaredDistance,
			}

			err := mbk.Fit(vectors)
			require.NoError(t, err)

			// Verify we have the correct number of centroids
			centroids := mbk.Centroids()
			require.Equal(t, 5, centroids.Count)
			require.Equal(t, vectors.Dims, centroids.Dims)

			// Test prediction works
			assignments := make([]uint64, vectors.Count)
			mbk.Predict(vectors, assignments)

			// Verify all assignments are within valid range
			for _, assignment := range assignments {
				require.Less(t, assignment, uint64(5))
			}
		})
	}
}

var (
	testDataset    = flag.String("dataset", "random", "Dataset to use for test. Small: random, glove, fashion, images, laion, dbpedia, clip. Large: dbpedia-openai-100k-angular, images-512-euclidean, fashion-mnist-784-euclidean, etc.")
	testK          = flag.Int("k", 10, "Number of clusters (K) to use for test")
	testInit       = flag.String("init", "random", "Initialization method (random, kmeans++)")
	testBatchSize  = flag.Int("batch-size", 0, "Batch size for mini-batch processing (0 = auto-select)")
	testIterations = flag.Int("iterations", 0, "Number of iterations to run (0 = use default)")
)

// TestMiniBatchKMeansPerformance runs the algorithm once on a dataset and prints
// runtime and convergence information. Use like:
//
//	./dev test pkg/sql/vecindex/cspann -f TestMiniBatchKMeansPerformance --test-args="-dataset=images -k=20 -init=kmeans++ -batch-size=500 -iterations=200"
//	./dev test pkg/sql/vecindex/cspann -f TestMiniBatchKMeansPerformance --test-args="-dataset=dbpedia-openai-100k-angular -k=50 -batch-size=1000 -iterations=100"
//
// Small datasets (local): random, glove, fashion, images, laion, dbpedia, clip
// Large datasets (downloaded): dbpedia-openai-100k-angular, images-512-euclidean, fashion-mnist-784-euclidean, gist-960-euclidean, sift-128-euclidean, laion-1m-test-ip
// Available init methods: random, kmeans++
func TestMiniBatchKMeansPerformance(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping performance test in short mode")
	}

	workspace := &workspace.T{}

	vectors := loadDatasetForTest(t, *testDataset)

	k := *testK
	if k <= 0 {
		k = 10
	}

	// Parse initialization method
	initMethod := InitRandom
	if *testInit == "kmeans++" {
		initMethod = InitKMeansPlusPlus
	}

	// Determine batch size - use flag if specified, otherwise auto-select
	batchSize := *testBatchSize
	if batchSize == 0 {
		batchSize = 1000
	}

	// Determine iterations - use flag if specified, otherwise use default
	iterations := *testIterations
	if iterations == 0 {
		iterations = 100
	}

	mbk := &MiniBatchKMeans{
		K:              k,
		BatchSize:      batchSize,
		MaxIterations:  iterations,
		InitMethod:     initMethod,
		Workspace:      workspace,
		Rand:           rand.New(rand.NewSource(42)),
		DistanceMetric: vecpb.L2SquaredDistance,
	}

	fmt.Printf("Running MiniBatchKMeans on dataset=%s (count=%d, dims=%d) with k=%d, batchSize=%d, iterations=%d, init=%s\n",
		*testDataset, vectors.Count, vectors.Dims, k, batchSize, iterations, *testInit)

	start := time.Now()
	require.NoError(t, mbk.Initialize(vectors))
	initDuration := time.Since(start)
	start = time.Now()
	require.NoError(t, mbk.Fit(vectors))
	duration := time.Since(start)

	// Print results
	fmt.Printf("Init: %v Runtime: %v\n", initDuration, duration)

	//// Calculate and print inertia (sum of squared distances to centroids)
	//assignments := make([]uint64, vectors.Count)
	//mbk.Predict(vectors, assignments)
	//
	//var inertia float64
	//centroids := mbk.Centroids()
	//for i := range vectors.Count {
	//	centroidIdx := assignments[i]
	//	distance := mbk.calculateDistance(vectors.At(i), centroids.At(int(centroidIdx)))
	//	inertia += float64(distance)
	//}
	//fmt.Printf("Inertia: %.2f\n", inertia)
}

// TestMiniBatchKMeansInitMethods compares different initialization methods
// and prints their performance characteristics. Use like:
//
//	./dev test pkg/sql/vecindex/cspann -f TestMiniBatchKMeansInitMethods --test-args="-dataset=fashion -k=12"
func TestMiniBatchKMeansInitMethods(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping performance test in short mode")
	}

	workspace := &workspace.T{}

	vectors := loadDatasetForTest(t, *testDataset)

	// Determine K value - use flag if specified, otherwise auto-select
	k := *testK
	if k <= 0 {
		k = 10
	}

	var initMethod InitializationMethod
	if *testInit == "random" {
		initMethod = InitRandom
	} else if *testInit == "kmeans++" {
		initMethod = InitKMeansPlusPlus
	}

	initMethods := []struct {
		name   string
		method InitializationMethod
	}{
		{"Random", InitRandom},
		{"KMeansPlusPlus", InitKMeansPlusPlus},
	}

	fmt.Printf("Comparing initialization methods on dataset=%s (count=%d, dims=%d) with k=%d\n",
		*testDataset, vectors.Count, vectors.Dims, k)

	for _, im := range initMethods {
		if initMethod != InitUnknown && im.method != initMethod {
			continue
		}
		mbk := &MiniBatchKMeans{
			K:              k,
			InitMethod:     im.method,
			Workspace:      workspace,
			Rand:           rand.New(rand.NewSource(42)),
			DistanceMetric: vecpb.L2SquaredDistance,
		}

		start := time.Now()
		err := mbk.Initialize(vectors)
		duration := time.Since(start)
		require.NoError(t, err)

		fmt.Printf("Runtime: %v\n", duration)

		//// Calculate inertia
		//assignments := make([]uint64, vectors.Count)
		//mbk.Predict(vectors, assignments)
		//
		//var inertia float64
		//centroids := mbk.Centroids()
		//for i := range vectors.Count {
		//	centroidIdx := assignments[i]
		//	distance := mbk.calculateDistance(vectors.At(i), centroids.At(int(centroidIdx)))
		//	inertia += float64(distance)
		//}
		//
		//fmt.Printf("%s: runtime=%v, iterations=%d, inertia=%.2f\n",
		//	im.name, duration, mbk.iterationsRun, inertia)
	}
}
