# Finite Naive Bayes Classifier

This pack is for learners, statistics users, solver contributors, and resource
consumers who need a small exact classifier example. It checks one finite
binary-feature Naive Bayes training table over exact rationals.

The point is narrow:

```text
finite counts -> smoothed likelihoods -> class scores -> posterior decision
```

Axeyum can replay those arithmetic facts and reject a malformed posterior
claim with checked QF_LRA/Farkas evidence. This does not prove general Naive
Bayes consistency, conditional-independence validity, calibration,
generalization, or floating-point classifier behavior.

## Audience

- Learners comparing finite probability tables with classifier scores.
- Educators showing where a modeling assumption enters a checked claim.
- Solver contributors looking for compact exact-rational probability pressure.
- Consumers querying statistics/classification resources by proof route.

## Concept Rows

- `field_statistics`
- `field_probability_theory`
- `curriculum_rationals`
- `curriculum_counting`
- `bridge_probability_mass_table`
- `bridge_finite_naive_bayes_shadow`
- `bridge_exact_vs_floating_arithmetic`
- `bridge_qf_lra_farkas_anatomy`

## What Is Checked

The validator recomputes:

- class counts and class priors;
- binary feature counts per class;
- Laplace-smoothed conditional likelihoods with `alpha = 1`;
- unnormalized class scores for the observation `(symptom=present,
  lab_positive=present)`;
- normalized posterior probabilities and the finite decision margin;
- a replay-only rejection of the false posterior `2/3`;
- a separate source-linked QF_LRA/Farkas rejection of the same posterior
  conflict.

## What Is Not Claimed

This pack does not claim:

- that the conditional-independence model is true for arbitrary data;
- that the classifier is Bayes-optimal;
- that posterior probabilities are calibrated;
- statistical consistency, sampling guarantees, or asymptotic inference;
- floating-point or library implementation correctness.

Those are theorem or numerical-honesty horizons.

## Validation

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-naive-bayes-classifier-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_naive_bayes_classifier_bad_posterior_artifact_emits_checked_farkas
```
