# Exact Finite K-Means Clustering Checks

This pack is for learners, proof contributors, solver contributors, and
resource consumers who need a small clustering example with an explicit trust
boundary.

The fixed object is a four-point rational dataset with two stated clusters. The
replay checks the assigned clusters, centroids, residuals, within-cluster
sum-of-squares, total squared deviation, and between-cluster decomposition
exactly. A separate QF_LRA/Farkas row rejects a malformed centroid-coordinate
claim.

## Audience

- Learners: see a k-means-style computation without floating-point ambiguity.
- Educators: show what a finite exact clustering shadow can and cannot prove.
- Proof contributors: inspect the Farkas route for the bad centroid row.
- Solver contributors: reuse a compact rational clustering/statistics artifact.
- Consumers: query the pack by statistics, optimization, numerical analysis,
  exact arithmetic, or finite-clustering concepts.

## Scope

The pack checks this finite rational dataset:

```text
(-2, 0) -> cluster 0
( 0, 0) -> cluster 0
( 4, 1) -> cluster 1
( 6, 1) -> cluster 1
```

It validates:

- fixed cluster assignment;
- exact centroids `(-1, 0)` and `(5, 1)`;
- point residuals and squared distances;
- within-cluster sum-of-squares `4`;
- total squared deviation `41`;
- between-cluster sum-of-squares `37`;
- a checked rejection of the false centroid claim `c0x = -1/2`.

## Limitations

This is not a proof of Lloyd-iteration convergence, k-means global optimality,
NP-hardness reductions, clustering consistency, model selection, randomized
initialization guarantees, or floating-point implementation correctness. Those
remain Lean/theorem or numerical-honesty horizon work.

## Validation

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-k-means-clustering-v0

cargo test -p axeyum-solver --test math_resource_lra_routes finite_k_means_clustering_bad_centroid_artifact_emits_checked_farkas
```
