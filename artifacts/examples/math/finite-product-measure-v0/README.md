# Finite Product Measure V0

This pack adds exact finite product-measure checks. It treats two finite
probability spaces as normalized finite measures, forms their Cartesian product,
and checks rectangle probabilities, marginals, and a finite Fubini calculation
by exact rational arithmetic.

The examples are:

- a product-measure table witness;
- a marginalization witness;
- a finite Fubini witness;
- checked rejection of false product probability and marginal claims;
- a product-measure and Fubini/Tonelli Lean-horizon row.

## Concepts

- `field_measure_theory`
- `field_probability_theory`
- `field_statistics`
- `field_real_analysis`
- `curriculum_sets`
- `curriculum_rationals`
- `curriculum_counting`

## Trust Story

The validator checks normalized finite factor distributions, verifies that each
product atom has probability `P(x) * Q(y)`, recomputes rectangle measures,
recomputes left and right marginals, and checks that a direct finite integral
matches both iterated finite sums. The false product-probability row is also
mirrored by a QF_LRA/Farkas regression over the replay-computed product mass,
and the false marginal row is mirrored by a source-linked Farkas regression
over the replay-computed row sum. All arithmetic is exact rational arithmetic.

This pack is checked finite evidence for bad product-probability and bad
marginal rows. It is not a proof of general product-measure construction,
Fubini/Tonelli, measurably indexed kernels, stochastic processes, or
almost-everywhere reasoning over arbitrary measure spaces.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-product-measure-v0
```
