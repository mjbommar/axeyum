# Checks

## Replay-Only Witnesses

- `knn-table-witness`
  - Expected: `sat`
  - Replays the six training points, class labels, two query points, and
    `k = 3`.

- `knn-distance-witness`
  - Expected: `sat`
  - Recomputes every squared Euclidean distance from each query to each
    training point.

- `knn-neighbor-witness`
  - Expected: `sat`
  - Checks the `k = 3` neighbor sets and the strict rank gaps `2 < 18` and
    `5 < 13`.

- `knn-vote-witness`
  - Expected: `sat`
  - Recounts the neighbor classes and checks the strict-majority predictions
    `positive` for `q1` and `negative` for `q2`.

- `bad-squared-distance-rejected`
  - Expected: `unsat`
  - Replays the coordinates and rejects the malformed claim that the squared
    distance from `q1` to `t4` is `16`.

## Checked Evidence

- `qf-lra-bad-squared-distance`
  - Expected: `unsat`
  - Source artifact:
    `artifacts/examples/math/finite-k-nearest-neighbors-v0/smt2/bad-squared-distance-farkas-conflict.smt2`
  - Route: QF_LRA/Farkas
  - Regression:
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_k_nearest_neighbors_bad_squared_distance_artifact_emits_checked_farkas`

## Horizon

- `general-nearest-neighbor-theory-lean-horizon`
  - Expected: `not-run`
  - Nearest-neighbor consistency, Bayes-risk bounds, curse-of-dimensionality
    behavior, metric/weighting/tie-breaking policy, choice of `k`,
    generalization, continuous feature spaces, and floating-point distance
    behavior are not checked by this pack.
