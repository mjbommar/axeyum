# Checks

## Replay Rows

- `training-count-witness`: replays the six training rows, class counts, and
  feature-present/absent counts per class.
- `smoothed-likelihood-witness`: recomputes Laplace-smoothed likelihoods with
  `alpha = 1` and binary feature cardinality `2`.
- `class-score-witness`: recomputes unnormalized class scores for the observed
  feature vector.
- `posterior-classification-witness`: normalizes the scores, checks posterior
  probabilities, and confirms the `positive` decision.
- `bad-posterior-rejected`: rejects the false posterior `2/3` by exact replay.

These rows are finite replay rows. They trust neither a statistical model nor a
floating-point implementation; they only check the committed rational table.

## Checked Row

- `qf-lra-bad-posterior`: checks the fixed scalar contradiction from the
  replayed posterior equation and the malformed posterior claim using the
  shared QF_LRA/Farkas proof route.

The source SMT-LIB artifact is:

```text
artifacts/examples/math/finite-naive-bayes-classifier-v0/smt2/bad-posterior-farkas-conflict.smt2
```

The route regression is:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes finite_naive_bayes_classifier_bad_posterior_artifact_emits_checked_farkas
```

## Horizon Row

- `general-naive-bayes-classifier-theory-lean-horizon`: records that
  conditional-independence assumptions, Bayes optimality, calibration,
  consistency, model selection, and floating-point classifier behavior require
  future theorem or numerical-honesty resources.
