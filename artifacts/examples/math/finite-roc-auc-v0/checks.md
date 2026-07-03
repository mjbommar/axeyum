# Checks

## Replay Rows

- `score-order-witness`: replays the six scored rows and recomputes the
  descending exact score order plus class counts.
- `threshold-operating-point-witness`: recomputes the threshold confusion
  counts and rates for `score >= 7/10`.
- `roc-staircase-witness`: recomputes the finite ROC staircase by scanning the
  descending score order.
- `auc-pairwise-witness`: recomputes pairwise AUC and trapezoid AUC.
- `bad-auc-rejected`: rejects the false AUC `3/4` by exact replay.

These rows are finite replay rows. They trust neither a statistical
generalization claim nor a floating-point implementation; they only check the
committed score table.

## Checked Row

- `qf-lra-bad-auc`: checks the fixed scalar contradiction from the replayed AUC
  equation and the malformed AUC claim using the shared QF_LRA/Farkas proof
  route.

The source SMT-LIB artifact is:

```text
artifacts/examples/math/finite-roc-auc-v0/smt2/bad-auc-farkas-conflict.smt2
```

The route regression is:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes finite_roc_auc_bad_auc_artifact_emits_checked_farkas
```

## Horizon Row

- `general-roc-auc-theory-lean-horizon`: records that ROC AUC threshold policy,
  tie conventions, calibration, confidence intervals, sampling guarantees,
  continuous score distributions, and floating-point classifier behavior
  require future theorem, statistical-inference, or numerical-honesty
  resources.
