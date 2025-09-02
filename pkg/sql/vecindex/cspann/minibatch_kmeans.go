// Copyright 2024 The Cockroach Authors.
//
// Use of this software is governed by the CockroachDB Software License
// included in the /LICENSE file.

package cspann

import (
	"math"
	"math/rand"

	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/cspann/workspace"
	"github.com/cockroachdb/cockroach/pkg/sql/vecindex/vecpb"
	"github.com/cockroachdb/cockroach/pkg/util/num32"
	"github.com/cockroachdb/cockroach/pkg/util/vector"
	"github.com/cockroachdb/errors"
)

// InitializationMethod specifies how initial centroids are selected.
type InitializationMethod int8

const (
	InitUnknown InitializationMethod = iota
	// InitRandom selects initial centroids randomly from the input vectors.
	// This is faster but may lead to poor initial clustering.
	InitRandom
	// InitKMeansPlusPlus uses the k-means++ algorithm for smarter centroid
	// initialization that spreads centroids throughout the data space.
	// This is slower but typically leads to better convergence.
	InitKMeansPlusPlus
)

// MiniBatchKMeans implements the mini-batch K-means algorithm described in
// "Web-Scale K-Means Clustering" by David Sculley.
// URL: https://dl.acm.org/doi/pdf/10.1145/1772690.1772862
//
// This is an online clustering algorithm that incrementally updates cluster
// centroids by processing small batches of data points at a time, making it
// suitable for large datasets that don't fit in memory.
//
// The algorithm maintains a set of k centroids and for each mini-batch:
// 1. Assigns each point to its nearest centroid
// 2. Updates centroids using a per-center learning rate that decreases over time
//
// This implementation supports multiple distance metrics (L2, InnerProduct, Cosine)
// consistent with the existing vecindex infrastructure.
type MiniBatchKMeans struct {
	// K is the number of clusters to form.
	K int
	// BatchSize is the size of mini-batches used for updates.
	BatchSize int
	// MaxIterations specifies the maximum number of mini-batch iterations.
	MaxIterations int
	// InitMethod specifies how initial centroids are selected.
	InitMethod InitializationMethod
	// Workspace is used to allocate temporary memory using stack allocators.
	Workspace *workspace.T
	// Rand is used to generate random numbers. If this is nil, then the global
	// random number generator is used instead.
	Rand *rand.Rand
	// DistanceMetric specifies which distance function to use when clustering
	// vectors. Lower distances indicate greater similarity.
	DistanceMetric vecpb.DistanceMetric

	// Internal state
	centroids    vector.Set
	perCenterCnt []int
	initialized  bool
	// Statistics
	iterationsRun int
}

func (mbk *MiniBatchKMeans) Initialize(vectors vector.Set) error {
	//if err := mbk.validateInputs(vectors); err != nil {
	//	return err
	//}
	mbk.initialize(vectors)
	return nil
}

// Fit trains the mini-batch K-means model on the given vector set.
func (mbk *MiniBatchKMeans) Fit(vectors vector.Set) error {
	//if err := mbk.validateInputs(vectors); err != nil {
	//	return err
	//}

	mbk.initialize(vectors)

	batchSize := mbk.BatchSize
	if batchSize == 0 {
		batchSize = 1000 // from paper
	}

	maxIterations := mbk.MaxIterations
	if maxIterations == 0 {
		maxIterations = 1000
	}

	tempBatch := mbk.Workspace.AllocVectorSet(batchSize, vectors.Dims)
	defer mbk.Workspace.FreeVectorSet(tempBatch)

	tempAssignments := mbk.Workspace.AllocUint64s(batchSize)
	defer mbk.Workspace.FreeUint64s(tempAssignments)

	for iter := 0; iter < maxIterations; iter++ {
		// Sample a mini-batch
		actualBatchSize := mbk.sampleBatch(vectors, tempBatch)
		if actualBatchSize == 0 {
			break
		}

		// Assign points to closest centroids
		mbk.assignToClosestCentroids(tempBatch.Slice(0, actualBatchSize), tempAssignments[:actualBatchSize])

		// Update centroids
		mbk.updateCentroids(tempBatch.Slice(0, actualBatchSize), tempAssignments[:actualBatchSize])
	}

	mbk.iterationsRun = maxIterations

	return nil
}

// Centroids returns the learned cluster centroids.
func (mbk *MiniBatchKMeans) Centroids() vector.Set {
	if !mbk.initialized {
		panic(errors.AssertionFailedf("MiniBatchKMeans not initialized"))
	}
	return mbk.centroids
}

// Predict assigns each vector in the input set to its closest cluster centroid.
func (mbk *MiniBatchKMeans) Predict(vectors vector.Set, assignments []uint64) {
	if !mbk.initialized {
		panic(errors.AssertionFailedf("MiniBatchKMeans not initialized"))
	}
	if len(assignments) != vectors.Count {
		panic(errors.AssertionFailedf(
			"assignments slice must have length %d, got %d", vectors.Count, len(assignments)))
	}

	mbk.assignToClosestCentroids(vectors, assignments)
}

// initialize sets up the initial centroids using k-means++ initialization.
func (mbk *MiniBatchKMeans) initialize(vectors vector.Set) {
	if mbk.initialized {
		return
	}

	// Allocate centroids
	mbk.centroids = mbk.Workspace.AllocVectorSet(mbk.K, vectors.Dims)
	mbk.perCenterCnt = make([]int, mbk.K)

	// Initialize centroids based on selected method
	switch mbk.InitMethod {
	case InitKMeansPlusPlus:
		mbk.initializeCentroidsKMeansPlusPlus(vectors)
	default: // InitRandom
		mbk.initializeCentroidsRandom(vectors)
	}

	mbk.initialized = true
}

// initializeCentroidsRandom randomly selects initial centroids from the input vectors.
// This is the default initialization method - faster but may lead to suboptimal clustering.
func (mbk *MiniBatchKMeans) initializeCentroidsRandom(vectors vector.Set) {
	// Use random permutation to select K unique indices
	var perm []int
	if mbk.Rand != nil {
		perm = mbk.Rand.Perm(vectors.Count)
	} else {
		perm = rand.Perm(vectors.Count)
	}

	for centroidIdx := 0; centroidIdx < mbk.K; centroidIdx++ {
		copy(mbk.centroids.At(centroidIdx), vectors.At(perm[centroidIdx]))
		mbk.perCenterCnt[centroidIdx] = 1
	}
}

// initializeCentroidsKMeansPlusPlus uses the k-means++ algorithm to select
// initial centroids that are well-spread throughout the data space.
func (mbk *MiniBatchKMeans) initializeCentroidsKMeansPlusPlus(vectors vector.Set) {
	// Select first centroid randomly
	var firstIdx int
	if mbk.Rand != nil {
		firstIdx = mbk.Rand.Intn(vectors.Count)
	} else {
		firstIdx = rand.Intn(vectors.Count)
	}
	copy(mbk.centroids.At(0), vectors.At(firstIdx))
	mbk.perCenterCnt[0] = 1

	tempDistances := mbk.Workspace.AllocFloats(vectors.Count)
	defer mbk.Workspace.FreeFloats(tempDistances)

	// Select remaining centroids
	for centroidIdx := 1; centroidIdx < mbk.K; centroidIdx++ {
		// Calculate distance to nearest existing centroid for each vector
		var distanceSum float32
		for i := range vectors.Count {
			minDistance := float32(math.MaxFloat32)
			for j := 0; j < centroidIdx; j++ {
				distance := mbk.calculateDistance(vectors.At(i), mbk.centroids.At(j))
				if distance < minDistance {
					minDistance = distance
				}
			}
			tempDistances[i] = minDistance
			distanceSum += minDistance
		}

		// Select next centroid with probability proportional to squared distance
		if distanceSum == 0 {
			// All remaining points are duplicates, select randomly
			var nextIdx int
			if mbk.Rand != nil {
				nextIdx = mbk.Rand.Intn(vectors.Count)
			} else {
				nextIdx = rand.Intn(vectors.Count)
			}
			copy(mbk.centroids.At(centroidIdx), vectors.At(nextIdx))
		} else {
			var rnd float32
			if mbk.Rand != nil {
				rnd = mbk.Rand.Float32() * distanceSum
			} else {
				rnd = rand.Float32() * distanceSum
			}

			var cumSum float32
			selectedIdx := 0
			for i := range vectors.Count {
				cumSum += tempDistances[i]
				if rnd <= cumSum {
					selectedIdx = i
					break
				}
			}
			copy(mbk.centroids.At(centroidIdx), vectors.At(selectedIdx))
		}
		mbk.perCenterCnt[centroidIdx] = 1
	}
}

// sampleBatch randomly samples a mini-batch from the input vectors.
func (mbk *MiniBatchKMeans) sampleBatch(vectors vector.Set, batch vector.Set) int {
	batchSize := batch.Count
	if batchSize > vectors.Count {
		batchSize = vectors.Count
	}

	for i := 0; i < batchSize; i++ {
		var idx int
		if mbk.Rand != nil {
			idx = mbk.Rand.Intn(vectors.Count)
		} else {
			idx = rand.Intn(vectors.Count)
		}
		copy(batch.At(i), vectors.At(idx))
	}

	return batchSize
}

// assignToClosestCentroids assigns each vector to its closest centroid.
func (mbk *MiniBatchKMeans) assignToClosestCentroids(vectors vector.Set, assignments []uint64) {
	for i := range vectors.Count {
		minDistance := float32(math.MaxFloat32)
		closestCentroid := 0

		for j := range mbk.K {
			distance := mbk.calculateDistance(vectors.At(i), mbk.centroids.At(j))
			if distance < minDistance {
				minDistance = distance
				closestCentroid = j
			}
		}

		assignments[i] = uint64(closestCentroid)
	}
}

// updateCentroids updates the centroids based on the assigned points using
// the per-center learning rate from the paper.
func (mbk *MiniBatchKMeans) updateCentroids(vectors vector.Set, assignments []uint64) {
	for i := range vectors.Count {
		centroidIdx := int(assignments[i])
		mbk.perCenterCnt[centroidIdx]++

		// Calculate learning rate: eta = 1 / per_center_cnt
		eta := 1.0 / float32(mbk.perCenterCnt[centroidIdx])

		// Update centroid: c = (1 - eta) * c + eta * x
		centroid := mbk.centroids.At(centroidIdx)
		vector := vectors.At(i)

		// centroid = (1 - eta) * centroid + eta * vector
		num32.Scale(1-eta, centroid)
		tempVector := mbk.Workspace.AllocVector(vectors.Dims)
		copy(tempVector, vector)
		num32.Scale(eta, tempVector)
		num32.Add(centroid, tempVector)
		mbk.Workspace.FreeVector(tempVector)

		// For spherical distance metrics, normalize the centroid
		if mbk.DistanceMetric == vecpb.CosineDistance || mbk.DistanceMetric == vecpb.InnerProductDistance {
			norm := num32.Norm(centroid)
			if norm > 0 {
				num32.Scale(1/norm, centroid)
			}
		}
	}
}

// calculateDistance computes the distance between two vectors based on the
// configured distance metric.
func (mbk *MiniBatchKMeans) calculateDistance(v1, v2 vector.T) float32 {
	switch mbk.DistanceMetric {
	case vecpb.L2SquaredDistance:
		return num32.L2SquaredDistance(v1, v2)
	case vecpb.InnerProductDistance:
		return -num32.Dot(v1, v2)
	case vecpb.CosineDistance:
		// Assume vectors are normalized
		return 1 - num32.Dot(v1, v2)
	default:
		panic(errors.AssertionFailedf("%s distance metric is not supported", mbk.DistanceMetric))
	}
}

// validateInputs checks that the configuration and input vectors are valid.
func (mbk *MiniBatchKMeans) validateInputs(vectors vector.Set) error {
	if vectors.Count == 0 {
		return errors.AssertionFailedf("cannot cluster empty vector set")
	}
	if mbk.K <= 0 {
		return errors.AssertionFailedf("K must be positive, got %d", mbk.K)
	}
	if mbk.K > vectors.Count {
		return errors.AssertionFailedf("K (%d) cannot be greater than number of vectors (%d)", mbk.K, vectors.Count)
	}

	switch mbk.DistanceMetric {
	case vecpb.L2SquaredDistance, vecpb.InnerProductDistance:
		// No additional validation needed
	case vecpb.CosineDistance:
		// Vectors should be unit vectors for cosine distance
		for i := range vectors.Count {
			norm := num32.Norm(vectors.At(i))
			if math.Abs(float64(norm-1.0)) > 1e-6 {
				return errors.AssertionFailedf("vectors must be normalized for cosine distance")
			}
		}
	default:
		return errors.AssertionFailedf("%s distance metric is not supported", mbk.DistanceMetric)
	}

	return nil
}

// Reset clears the internal state, allowing the algorithm to be reused.
func (mbk *MiniBatchKMeans) Reset() {
	if mbk.initialized {
		mbk.Workspace.FreeVectorSet(mbk.centroids)
		mbk.centroids = vector.Set{}
		mbk.perCenterCnt = nil
		mbk.initialized = false
	}
	mbk.iterationsRun = 0
}
