# Numerical Linear Algebra V0

This pack covers the first exact numerical-analysis slice for the
`numerical_analysis` field row. It uses rational matrices and vectors to model
the checks that sit underneath numerical linear algebra: residuals, interval
solution boxes, and one-step iterative-method error bounds.

The pack does not use floating-point arithmetic. It is a bridge from the
existing exact rational linear-algebra pack toward future numerical-honesty
resources for rounding, backward error, conditioning, and convergence.

The examples are:

- residual infinity-norm replay for an approximate solution;
- exact solution replay inside a rational interval box;
- one Jacobi iteration step with an exact row-sum contraction check;
- checked QF_LRA/Farkas rejection of a false residual bound.

## Concepts

- `field_numerical_analysis`
- `field_linear_algebra`
- `field_optimization_and_convexity`
- `curriculum_linear_algebra`
- `curriculum_rationals`
- `curriculum_reals`

## Trust Story

The validator parses all scalars as exact rational strings. It recomputes
matrix-vector products, residual vectors, infinity norms, interval membership,
Jacobi updates, exact solution residuals, and the row-sum contraction bound.

This is checked Farkas evidence for the bad-bound row and replay-only evidence
for the positive witnesses. Floating-point stability and general convergence
theorems remain future work.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/numerical-linear-algebra-v0
```
