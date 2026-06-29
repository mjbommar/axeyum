# Convexity Rational V0

This pack adds exact rational convexity examples for the
`optimization_and_convexity` field. It complements `linear-optimization-v0`:
that pack checks LP feasibility and a tiny Farkas certificate, while this pack
checks finite convexity, monotonicity, and threshold facts.

The examples are:

- a midpoint Jensen replay for `f(x) = x^2`;
- nonnegative second differences on an equally spaced finite grid;
- a finite monotonicity/threshold replay for `g(x) = 3x - 2`;
- checked rejection of a bad midpoint-convexity claim;
- a general convex-analysis Lean-horizon row.

## Concepts

- `field_optimization_and_convexity`
- `field_real_analysis`
- `field_linear_algebra`
- `curriculum_reals`
- `curriculum_rationals`
- `curriculum_linear_algebra`

## Trust Story

The validator uses exact `Fraction` arithmetic. It recomputes polynomial
values, midpoint averages, finite grid second differences, affine sample
values, and the bad midpoint counterexample from the raw pack data.

This is finite checked evidence. It is not a proof of Jensen's inequality in
general, separation theorems, SDP duality, or convergence of convex
optimization algorithms.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/convexity-rational-v0
```
