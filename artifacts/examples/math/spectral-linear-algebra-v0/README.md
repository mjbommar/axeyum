# Spectral Linear Algebra V0

This pack adds the first exact finite spectral-linear-algebra slice. It uses a
single rational symmetric `2x2` matrix, so every check is finite and exact.

The examples are:

- an eigenpair witness;
- an orthogonal eigenbasis witness;
- a Rayleigh quotient witness;
- a spectral decomposition replay;
- checked QF_LRA/Farkas rejection of a false eigenpair.

## Concepts

- `field_linear_algebra`
- `field_functional_analysis_and_operator_theory`
- `field_numerical_analysis`
- `field_optimization_and_convexity`
- `curriculum_linear_algebra`
- `curriculum_rationals`
- `curriculum_reals`

## Trust Story

The validator parses every matrix and vector entry as an exact rational string.
It recomputes matrix-vector products, scalar-vector products, dot products,
Rayleigh quotient numerators and denominators, and `P*D*P^-1` reconstruction.

This pack is checked finite evidence for the bad eigenpair row and replay-only
evidence for the positive witnesses. The bad eigenpair row additionally links
a `QF_LRA` SMT-LIB artifact and a solver regression that emits independently
rechecked `UnsatFarkas` evidence for the first-component conflict
`eigen_image_0 = 3` versus `eigen_image_0 = 2`. General spectral theorems,
compact operators, numerical eigensolvers, and spectral convergence remain
proof or numerical-horizon material.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/spectral-linear-algebra-v0
```
