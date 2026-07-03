# Checks

## Replay Rows

- `confusion-count-witness`: replays the eight actual/predicted rows and
  recomputes the confusion counts plus class totals.
- `accuracy-witness`: recomputes exact accuracy as `(TP + TN) / total`.
- `precision-recall-witness`: recomputes precision, recall/sensitivity,
  specificity, negative predictive value, false-positive rate, and
  false-negative rate.
- `f1-balanced-accuracy-witness`: recomputes balanced accuracy, F1, and
  Jaccard index.
- `bad-precision-rejected`: rejects the false precision `3/4` by exact replay.

These rows are finite replay rows. They trust neither a statistical
generalization claim nor a floating-point implementation; they only check the
committed count table.

## Checked Row

- `qf-lra-bad-precision`: checks the fixed scalar contradiction from the
  replayed precision equation and the malformed precision claim using the
  shared QF_LRA/Farkas proof route.

The source SMT-LIB artifact is:

```text
artifacts/examples/math/finite-confusion-matrix-v0/smt2/bad-precision-farkas-conflict.smt2
```

The route regression is:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes finite_confusion_matrix_bad_precision_artifact_emits_checked_farkas
```

## Horizon Row

- `general-classifier-metrics-theory-lean-horizon`: records that classifier
  calibration, confidence intervals, threshold theory, ROC/AUC, ranking
  metrics, sampling guarantees, and floating-point classifier behavior require
  future theorem, statistical-inference, or numerical-honesty resources.
