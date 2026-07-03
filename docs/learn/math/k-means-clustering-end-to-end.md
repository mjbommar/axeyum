# Exact Finite K-Means Clustering Checks

This page follows
[finite-k-means-clustering-v0](../../../artifacts/examples/math/finite-k-means-clustering-v0/).
It shows how Axeyum treats a clustering computation as exact finite rational
replay, not as a theorem about arbitrary k-means or a floating-point
implementation.

## The Finite Object

The pack fixes four observations and two cluster labels:

```text
(-2, 0) -> cluster 0
( 0, 0) -> cluster 0
( 4, 1) -> cluster 1
( 6, 1) -> cluster 1
```

The labels are not discovered by the checker. They are part of the finite
object being audited. Axeyum then recomputes the consequences of that object.

## Centroids

Cluster 0 has centroid:

```text
((-2 + 0) / 2, (0 + 0) / 2) = (-1, 0)
```

Cluster 1 has centroid:

```text
((4 + 6) / 2, (1 + 1) / 2) = (5, 1)
```

Each point is distance `1` squared from its assigned centroid, so:

```text
WCSS = 1 + 1 + 1 + 1 = 4
```

## Decomposition

The global centroid is:

```text
g = (2, 1/2)
```

The total squared deviation from `g` is:

```text
65/4 + 17/4 + 17/4 + 65/4 = 41
```

The two cluster centroids are each squared distance `37/4` from `g`. Weighted
by two points per cluster:

```text
between = 2 * 37/4 + 2 * 37/4 = 37
within  = 4
total   = 37 + 4 = 41
```

This is the finite clustering analogue of a variance decomposition. The pack
checks the arithmetic for this fixed assignment only.

## The Bad Claim

The malformed row claims the first centroid x-coordinate is `-1/2`. The source
SMT-LIB artifact isolates the contradiction:

```text
2 * c0x = -2
c0x = -1/2
```

The QF_LRA route emits `UnsatFarkas` evidence and independently rechecks it.

## Trust Boundary

```text
finite replay        -> recompute clusters, centroids, residuals, objective
checked evidence     -> reject the malformed centroid-coordinate equality
theorem horizon      -> Lloyd convergence, global optimality, statistics, FP
```

This is Axeyum's core pattern in a clustering setting: untrusted search may
propose labels, centroids, or a corrupted scalar, but trusted small checking
recomputes the exact finite claim being displayed.

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-k-means-clustering-v0

cargo test -p axeyum-solver --test math_resource_lra_routes finite_k_means_clustering_bad_centroid_artifact_emits_checked_farkas

python3 scripts/query-foundational-resources.py checks --pack finite-k-means-clustering-v0 --route Farkas --proof-status checked --require-any
```

The first command checks the finite model, the second command checks the Farkas
evidence route, and the third command verifies that consumers can find the
promoted checked row through the public JSON/query boundary.
