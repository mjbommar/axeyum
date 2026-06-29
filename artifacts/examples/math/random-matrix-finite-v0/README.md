# Random Matrix Finite V0

This pack is the first finite random-matrix bridge between linear algebra,
probability, statistics, and numerical analysis. It does not claim asymptotic
random matrix theory. It checks small matrix-valued probability distributions
exactly.

The examples are:

- exact trace, trace-square, determinant, and invertibility moments for a
  uniform distribution over diagonal sign matrices;
- exact expected Gram matrix replay for the same distribution;
- exact rank probabilities for a finite mixture of rank `0`, `1`, and `2`
  matrices;
- checked QF_LRA/Farkas rejection of a false trace-square moment.

## Concepts

- `field_probability_theory`
- `field_statistics`
- `field_linear_algebra`
- `field_numerical_analysis`
- `curriculum_counting`
- `curriculum_rationals`
- `curriculum_linear_algebra`

## Trust Story

The validator parses atom probabilities and matrix entries as exact rational
strings. It checks that matrix-valued atom probabilities sum to `1`, then
recomputes traces, determinants, matrix ranks, `A^T A`, weighted expectations,
and the rejected bad moment without floating-point arithmetic. The bad
trace-square row additionally links a `QF_LRA` SMT-LIB artifact and a solver
regression that emits independently rechecked `UnsatFarkas` evidence for
`expected_trace_square = 2` plus the false claim `expected_trace_square = 1`.

This pack gives a concrete finite slice for random-matrix reasoning. Spectral
laws, concentration inequalities, floating-point simulation claims, and
high-dimensional limits remain proof/numerical-horizon material.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/random-matrix-finite-v0
```
