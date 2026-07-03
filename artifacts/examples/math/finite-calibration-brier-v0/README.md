# Finite Calibration And Brier Score

This pack is for learners, statistics users, solver contributors, and resource
consumers who need a small exact probabilistic-classifier example. It checks
one finite binary forecast table over exact rational probabilities, two
calibration bins, expected calibration error, and Brier score.

The point is narrow:

```text
probability forecasts -> calibration bins -> exact ECE -> exact Brier score
```

Axeyum can replay those arithmetic facts and reject a malformed Brier-score
claim with checked QF_LRA/Farkas evidence. This does not prove calibration of a
model family, estimate uncertainty, choose bins, prove proper-scoring-rule
theorems, or check floating-point probability implementations.

## Audience

- Learners comparing probabilistic classifier outputs with exact labels.
- Educators showing how finite calibration bins and Brier score become rational
  arithmetic.
- Solver contributors looking for compact exact-rational statistics pressure.
- Consumers querying statistics/classification resources by proof route.

## Concept Rows

- `field_statistics`
- `field_probability_theory`
- `curriculum_counting`
- `curriculum_rationals`
- `bridge_probability_mass_table`
- `bridge_finite_classifier_metrics_shadow`
- `bridge_finite_calibration_brier_shadow`
- `bridge_exact_vs_floating_arithmetic`
- `bridge_qf_lra_farkas_anatomy`

## What Is Checked

The validator recomputes:

- the six exact probabilistic classifier rows;
- positive, negative, and total class counts;
- two fixed calibration bins split at probability `1/2`;
- average predicted probability, observed positive rate, absolute gap, and
  weighted gap for each bin;
- expected calibration error `1/10`;
- per-row Brier squared errors and mean Brier score `71/300`;
- a replay-only rejection of the false Brier score `1/5`;
- a separate source-linked QF_LRA/Farkas rejection of the same Brier conflict.

## What Is Not Claimed

This pack does not claim:

- that the chosen two-bin calibration summary is canonical or optimal;
- a general calibration theorem;
- proper-scoring-rule optimality or strict propriety;
- sampling guarantees, risk bounds, or confidence intervals;
- continuous score-distribution theory;
- floating-point or library implementation correctness.

Those are theorem, statistical-inference, or numerical-honesty horizons.

## Validation

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-calibration-brier-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_calibration_brier_bad_brier_score_artifact_emits_checked_farkas
```
