# Exact Statistical Tests V0

This pack adds the first exact finite statistical-test slice for the
`statistics` field row. It treats p-values as rational finite sums, not as
floating-point approximations.

The examples are:

- a one-sided exact binomial tail probability;
- a hypergeometric point probability for a fixed `2x2` table;
- a one-sided Fisher exact-test p-value under fixed margins;
- a probability-ordered two-sided Fisher exact-test p-value under fixed margins;
- checked QF_LRA/Farkas rejection of false Fisher left-tail and two-sided
  p-values;
- checked rejection of a false binomial p-value;
- a QF_LIA/Diophantine certificate for the rejected binomial tail numerator.

## Concepts

- `field_statistics`
- `field_probability_theory`
- `field_discrete_math`
- `curriculum_counting`
- `curriculum_rationals`
- `curriculum_naturals`

## Trust Story

The validator parses probabilities as exact rational strings and count tables
as finite nonnegative integers. It recomputes binomial coefficients,
hypergeometric point probabilities, one-sided finite tails, probability-ordered
two-sided Fisher sums, and bad p-value refutations exactly.

This is checked finite evidence for the bad p-value rows, plus solver-form
Farkas evidence for the rejected Fisher p-values and Diophantine evidence for
the rejected binomial tail count. Positive witnesses remain replay-only.
Asymptotic tests, normal approximations, floating-point statistical libraries,
calibration, and model-selection claims remain numerical-honesty material.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/exact-statistical-tests-v0
```
