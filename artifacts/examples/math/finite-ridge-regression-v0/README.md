# Finite Ridge Regression V0

This pack extends the exact regression resources with one deterministic ridge
regression transcript over rational data. It checks the regularized normal
equations, fitted values, residuals, coefficient shrinkage, and the
regularized objective without using floating point.

The pack covers:

- exact replay of `X^T X + lambda I`;
- exact ridge coefficients for `lambda = 1`;
- residual and penalty arithmetic for one fixed fit;
- comparison against the unregularized least-squares coefficients under the
  ridge objective;
- replay rejection of a bad ridge coefficient;
- checked rejection of the same bad coefficient through QF_LRA/Farkas;
- a Lean-horizon row for general ridge-regression theory.

## Concepts

- `field_statistics`
- `field_linear_algebra`
- `field_optimization_and_convexity`
- `field_numerical_analysis`
- `curriculum_rationals`
- `curriculum_linear_algebra`
- `curriculum_reals`
- `bridge_residual_bound`
- `bridge_inner_product_projection`
- `bridge_exact_vs_floating_arithmetic`

## Trust Story

The validator parses the design matrix, response vector, regularization
parameter, coefficients, fitted values, residuals, normal equations, residual
sum of squares, penalty, and regularized objective as exact rational strings.
It recomputes every matrix-vector product and dot product.

The malformed coefficient row is checked twice: finite replay recomputes
`beta0 = 4/5`, and the separate QF_LRA artifact isolates the final linear
conflict between the regularized normal equations and `beta0 = 1`.

This is a finite deterministic regression replay pack. It does not claim
general ridge optimality theorems, model-selection theory, statistical
inference, cross-validation, floating-point linear algebra, or numerical
stability.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-ridge-regression-v0
```
