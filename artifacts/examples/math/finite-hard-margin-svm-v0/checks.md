# Checks

## Replay-Only Witnesses

- `svm-table-witness`
  - Expected: `sat`
  - Replays the six training points, labels, classes, and the committed
    hyperplane `w = (1/2, 1/2)`, `b = -1`.

- `svm-feasibility-witness`
  - Expected: `sat`
  - Recomputes every functional margin `y * (w . x + b)`: `1, 1, 2, 3/2, 2, 2`
    with minimum `1`, and requires the support vectors to sit exactly on the
    margin.

- `svm-kkt-witness`
  - Expected: `sat`
  - Checks multiplier nonnegativity, the multiplier/label balance
    `sum(alpha*y) = 0`, stationarity `w = sum(alpha*y*x)`, and complementary
    slackness `alpha * (margin - 1) = 0` for every point.

- `svm-duality-witness`
  - Expected: `sat`
  - Recomputes `||w||^2 = 1/2`, the primal objective `1/4`, the dual
    objective `1/4`, and the zero duality gap.

- `bad-bias-rejected`
  - Expected: `unsat`
  - Replays the support-vector margin equalities and rejects the malformed
    claim that the maximum-margin bias is `-1/2`.

## Checked Evidence

- `qf-lra-bad-bias`
  - Expected: `unsat`
  - Source artifact:
    `artifacts/examples/math/finite-hard-margin-svm-v0/smt2/bad-bias-farkas-conflict.smt2`
  - Route: QF_LRA/Farkas
  - Regression:
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_hard_margin_svm_bad_bias_artifact_emits_checked_farkas`

## Horizon

- `general-svm-theory-lean-horizon`
  - Expected: `not-run`
  - Strong duality and KKT sufficiency, maximum-margin optimality and
    uniqueness, geometric-margin theory, soft-margin/hinge-loss and kernel
    variants, SMO/solver behavior, generalization bounds, and floating-point
    training behavior are not checked by this pack.
