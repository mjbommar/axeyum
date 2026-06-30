# Finite Integration V0

This pack adds exact finite integration and expectation checks. It treats a
finite probability table as a normalized finite measure and checks simple
functions by exact rational weighted sums.

The examples are:

- a simple-function integral witness;
- an indicator-integral witness;
- an integral-linearity witness;
- checked rejection of a false expectation claim;
- a Lebesgue-integration Lean-horizon row.

## Concepts

- `field_measure_theory`
- `field_probability_theory`
- `field_statistics`
- `field_real_analysis`
- `curriculum_sets`
- `curriculum_rationals`
- `curriculum_counting`

## Trust Story

The validator checks normalized finite atom probabilities, recomputes
`sum_x f(x) * P(x)`, recomputes event measures, and checks finite linearity of
the integral. The false expectation row is also mirrored by a QF_LRA/Farkas
regression over the replay-computed integral. All arithmetic is exact rational
arithmetic.

This pack is checked finite evidence for the bad expectation row. It is not a
proof of Lebesgue integration, monotone convergence, dominated convergence,
Fubini/Tonelli, or almost-everywhere reasoning over arbitrary measure spaces.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-integration-v0
```
