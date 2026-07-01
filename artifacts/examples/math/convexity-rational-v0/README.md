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
- checked rejection of a bad affine-threshold claim;
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
values, the bad midpoint counterexample, and the bad affine-threshold
shortfall from the raw pack data. The bad midpoint-convexity row also has an
Axeyum regression that builds the division-free `QF_LRA` contradiction
`2*f(midpoint) <= f(left)+f(right)`, emits `UnsatFarkas` evidence, and rechecks
that evidence independently. The bad affine-threshold row parses a source-level
SMT-LIB artifact for the exact shortfall `1 - g(1/2) = 3/2` and checks the
Farkas refutation of the nonpositive-shortfall claim. The positive finite rows
remain exact replay-only until they route through model evidence.

This is finite checked evidence. It is not a proof of Jensen's inequality in
general, separation theorems, SDP duality, or convergence of convex
optimization algorithms.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/convexity-rational-v0
cargo test -p axeyum-solver --test math_resource_lra_routes convexity_bad_
```
