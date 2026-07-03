# Finite Precision Recall Classifier Ranking

This pack is for learners, statistics users, solver contributors, and resource
consumers who need a small exact precision-recall example. It checks one finite
binary score table over exact rational scores, threshold precision/recall
counts, a precision-recall curve, and average precision.

The point is narrow:

```text
scored rows -> score order -> threshold precision/recall -> PR curve -> exact AP
```

Axeyum can replay those arithmetic facts and reject a malformed average
precision claim with checked QF_LRA/Farkas evidence. This does not choose a
threshold, prove calibration, estimate uncertainty, cover general tie
conventions, or prove anything about continuous score distributions.

## Audience

- Learners comparing classifier score rankings with exact precision-recall
  definitions.
- Educators showing how finite ranked hits become rational average precision.
- Solver contributors looking for compact exact-rational statistics pressure.
- Consumers querying statistics/classification resources by proof route.

## Concept Rows

- `field_statistics`
- `field_probability_theory`
- `curriculum_counting`
- `curriculum_rationals`
- `bridge_probability_mass_table`
- `bridge_finite_classifier_metrics_shadow`
- `bridge_finite_roc_auc_shadow`
- `bridge_finite_precision_recall_shadow`
- `bridge_exact_vs_floating_arithmetic`
- `bridge_qf_lra_farkas_anatomy`

## What Is Checked

The validator recomputes:

- the descending exact score order;
- positive, negative, and total class counts;
- the threshold operating point for `score >= 7/10`;
- precision, recall, and F1 at that threshold;
- the precision-recall curve obtained by scanning the descending score order;
- average precision from precision at each positive hit;
- a replay-only rejection of the false average precision `3/4`;
- a separate source-linked QF_LRA/Farkas rejection of the same average
  precision conflict.

## What Is Not Claimed

This pack does not claim:

- that the threshold `7/10` is optimal;
- calibration, risk bounds, or confidence intervals;
- a general theorem about precision-recall curves;
- tie-policy coverage beyond this tie-free finite table;
- continuous score-distribution theory;
- floating-point or library implementation correctness.

Those are theorem, statistical-inference, or numerical-honesty horizons.

## Validation

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-precision-recall-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_precision_recall_bad_average_precision_artifact_emits_checked_farkas
```
