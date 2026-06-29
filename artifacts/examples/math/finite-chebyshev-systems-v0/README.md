# Finite Chebyshev Systems V0

This pack adds exact finite checks for the Chebyshev-system gap in the math
field spine. It uses rational sample points and small polynomial bases to
replay finite unisolvence, interpolation, and alternation-style sign evidence.

The examples are:

- a Vandermonde unisolvence witness for the basis `1, x, x^2`;
- an interpolation replay from coefficients to sample values;
- an alternating residual sign-pattern witness on three sample points;
- checked rejection of a degenerate duplicate-node interpolation grid;
- a general Chebyshev-space Lean-horizon row.

## Concepts

- `field_functional_analysis_and_operator_theory`
- `field_numerical_analysis`
- `field_linear_algebra`
- `field_real_analysis`
- `curriculum_linear_algebra`
- `curriculum_polynomials`
- `curriculum_reals`
- `curriculum_rationals`

## Trust Story

The validator recomputes polynomial-basis evaluation matrices, exact rational
determinants, interpolation matrix-vector products, residual values, signs, and
degenerate-grid null vectors. The bad-grid row is checked by showing the
evaluation matrix has determinant zero and a nonzero coefficient vector that
vanishes on all listed sample points.

This pack is finite checked evidence. It is not a proof of general Chebyshev
systems, Haar spaces, minimax approximation, alternation theorems, compactness
arguments, or infinite-dimensional functional analysis.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chebyshev-systems-v0
```
