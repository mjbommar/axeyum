# Finite Confusion Matrix Classifier Metrics

This pack is for learners, statistics users, solver contributors, and resource
consumers who need a small exact classifier-evaluation example. It checks one
finite binary classifier result table over exact integer counts and rational
metrics.

The point is narrow:

```text
actual/predicted rows -> TP/FP/TN/FN counts -> exact rational metrics
```

Axeyum can replay those arithmetic facts and reject a malformed precision
claim with checked QF_LRA/Farkas evidence. This does not prove classifier
generalization, calibration, threshold quality, ROC/AUC behavior, uncertainty
intervals, or floating-point implementation behavior.

## Audience

- Learners comparing classifier outputs with exact metric definitions.
- Educators showing how count tables become rational statistics.
- Solver contributors looking for compact exact-rational statistics pressure.
- Consumers querying statistics/classification resources by proof route.

## Concept Rows

- `field_statistics`
- `field_probability_theory`
- `curriculum_counting`
- `curriculum_rationals`
- `bridge_probability_mass_table`
- `bridge_finite_classifier_metrics_shadow`
- `bridge_exact_vs_floating_arithmetic`
- `bridge_qf_lra_farkas_anatomy`

## What Is Checked

The validator recomputes:

- true-positive, false-positive, true-negative, and false-negative counts;
- actual-class and predicted-class totals;
- accuracy, precision, recall/sensitivity, specificity, negative predictive
  value, false-positive rate, false-negative rate, balanced accuracy, F1, and
  Jaccard index;
- a replay-only rejection of the false precision `3/4`;
- a separate source-linked QF_LRA/Farkas rejection of the same precision
  conflict.

## What Is Not Claimed

This pack does not claim:

- that the classifier is accurate on unseen data;
- calibration, risk bounds, or confidence intervals;
- threshold selection, ROC/AUC, precision-recall curve, or ranking quality;
- statistical consistency or sampling guarantees;
- floating-point or library implementation correctness.

Those are theorem, statistical-inference, or numerical-honesty horizons.

## Validation

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-confusion-matrix-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_confusion_matrix_bad_precision_artifact_emits_checked_farkas
```
