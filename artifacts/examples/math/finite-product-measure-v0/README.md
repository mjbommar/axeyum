# Finite Product Measure V0

This pack adds exact finite product-measure checks. It treats two finite
probability spaces as normalized finite measures, forms their Cartesian product,
and checks rectangle probabilities, marginals, and a finite Fubini calculation
by exact rational arithmetic.

The examples are:

- a product-measure table witness;
- a marginalization witness;
- a finite Fubini witness;
- checked rejection of a false product probability;
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
matches both iterated finite sums. All arithmetic is exact rational arithmetic.

This pack is checked finite evidence for the bad product-probability row. It is
not a proof of general product-measure construction, Fubini/Tonelli, measurably
indexed kernels, stochastic processes, or almost-everywhere reasoning over
arbitrary measure spaces.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-product-measure-v0
```
