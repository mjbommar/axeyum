# Checks

## Replay Rows

- `score-order-witness`: replays the six scored rows and recomputes the
  descending exact score order plus class counts.
- `precision-recall-threshold-witness`: recomputes the threshold counts and
  precision/recall/F1 for `score >= 7/10`.
- `precision-recall-curve-witness`: recomputes the finite precision-recall
  curve by scanning the descending score order.
- `average-precision-witness`: recomputes average precision from precision at
  each positive hit.
- `bad-average-precision-rejected`: rejects the false average precision `3/4`
  by exact replay.

These rows are finite replay rows. They trust neither a statistical
generalization claim nor a floating-point implementation; they only check the
committed score table.

## Checked Row

- `qf-lra-bad-average-precision`: checks the fixed scalar contradiction from
  the replayed average-precision equation and the malformed average-precision
  claim using the shared QF_LRA/Farkas proof route.

The source SMT-LIB artifact is:

```text
artifacts/examples/math/finite-precision-recall-v0/smt2/bad-average-precision-farkas-conflict.smt2
```

The route regression is:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes finite_precision_recall_bad_average_precision_artifact_emits_checked_farkas
```

## Horizon Row

- `general-precision-recall-theory-lean-horizon`: records that
  precision-recall threshold policy, tie conventions, calibration, confidence
  intervals, sampling guarantees, continuous score distributions, and
  floating-point classifier behavior require future theorem,
  statistical-inference, or numerical-honesty resources.
