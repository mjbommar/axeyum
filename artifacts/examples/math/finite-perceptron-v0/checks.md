# Checks

## Replay-Only Witnesses

- `perceptron-table-witness`
  - Expected: `sat`
  - Replays the four training points, labels, augmented bias components, and
    the zero initial weight vector.

- `perceptron-update-witness`
  - Expected: `sat`
  - Recomputes every presented step: dot-product score, mistake condition,
    and weight update; exactly two updates ending at `(-1, 3, 0)`.

- `perceptron-convergence-witness`
  - Expected: `sat`
  - Checks that the final weights classify every training point with a
    strictly positive functional margin.

- `perceptron-margin-witness`
  - Expected: `sat`
  - Recomputes the final functional margins `5, 5, 7, 7` and the minimum
    margin `5`.

- `bad-weight-update-rejected`
  - Expected: `unsat`
  - Replays the trace and rejects the malformed claim that the first weight
    coordinate after step 2 is `1`.

## Checked Evidence

- `qf-lra-bad-weight-update`
  - Expected: `unsat`
  - Source artifact:
    `artifacts/examples/math/finite-perceptron-v0/smt2/bad-weight-update-farkas-conflict.smt2`
  - Route: QF_LRA/Farkas
  - Regression:
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_perceptron_bad_weight_update_artifact_emits_checked_farkas`

## Horizon

- `general-perceptron-theory-lean-horizon`
  - Expected: `not-run`
  - The Novikoff mistake bound, convergence theorems, geometric-margin
    theory, non-separable/kernel/averaged variants, learning-rate policy,
    generalization, and floating-point training behavior are not checked by
    this pack.
