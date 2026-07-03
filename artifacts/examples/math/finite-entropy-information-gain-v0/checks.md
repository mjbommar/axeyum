# Checks

## Replay-Only Witnesses

- `entropy-table-witness`
  - Expected: `sat`
  - Replays the finite table, feature values, class labels, class totals, and
    the dyadic-proportion restriction.

- `root-entropy-witness`
  - Expected: `sat`
  - Recomputes the root entropy `1` bit.

- `split-entropy-witness`
  - Expected: `sat`
  - Recomputes the `color` weighted entropy `1/2`, the `shape` weighted
    entropy `1`, and their information gains.

- `best-information-gain-witness`
  - Expected: `sat`
  - Checks that `color` is strictly better than `shape` for the committed
    candidate set.

- `bad-weighted-entropy-rejected`
  - Expected: `unsat`
  - Replays the table and rejects the malformed claim that the `color` split
    has weighted entropy `3/4`.

## Checked Evidence

- `qf-lra-bad-weighted-entropy`
  - Expected: `unsat`
  - Source artifact:
    `artifacts/examples/math/finite-entropy-information-gain-v0/smt2/bad-weighted-entropy-farkas-conflict.smt2`
  - Route: QF_LRA/Farkas
  - Regression:
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_entropy_information_gain_bad_weighted_entropy_artifact_emits_checked_farkas`

## Horizon

- `general-entropy-information-gain-lean-horizon`
  - Expected: `not-run`
  - Entropy at non-dyadic proportions, log-loss/mutual-information variants,
    entropy concavity, greedy optimality, pruning, tie-breaking policy,
    generalization, confidence intervals, continuous thresholds, and
    floating-point logarithm or training behavior are not checked by this
    pack.
