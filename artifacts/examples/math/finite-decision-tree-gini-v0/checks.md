# Checks

## Replay-Only Witnesses

- `decision-tree-table-witness`
  - Expected: `sat`
  - Replays the finite table, feature values, class labels, and class totals.

- `root-gini-witness`
  - Expected: `sat`
  - Recomputes the root Gini impurity `1/2`.

- `split-gini-witness`
  - Expected: `sat`
  - Recomputes the `color` weighted impurity `3/8`, the `shape` weighted
    impurity `1/2`, and their impurity gains.

- `best-split-witness`
  - Expected: `sat`
  - Checks that `color` is strictly better than `shape` for the committed
    candidate set.

- `bad-weighted-gini-rejected`
  - Expected: `unsat`
  - Replays the table and rejects the malformed claim that the `color` split
    has weighted Gini impurity `1/2`.

## Checked Evidence

- `qf-lra-bad-weighted-gini`
  - Expected: `unsat`
  - Source artifact:
    `artifacts/examples/math/finite-decision-tree-gini-v0/smt2/bad-weighted-gini-farkas-conflict.smt2`
  - Route: QF_LRA/Farkas
  - Regression:
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_decision_tree_gini_bad_weighted_gini_artifact_emits_checked_farkas`

## Horizon

- `general-decision-tree-theory-lean-horizon`
  - Expected: `not-run`
  - Greedy optimality, pruning, tie-breaking policy, entropy/log-loss splitting,
    generalization, confidence intervals, continuous thresholds, and
    floating-point training behavior are not checked by this pack.
