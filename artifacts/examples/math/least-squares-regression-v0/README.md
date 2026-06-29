# Least Squares Regression V0

This pack extends the `statistics` field with exact ordinary least-squares
regression checks over tiny rational datasets. It connects descriptive
statistics to linear algebra and optimization without using floating point.

The pack covers:

- exact normal-equation replay for a perfect affine fit;
- residual orthogonality for a non-perfect least-squares fit;
- mean-baseline residual-sum-of-squares comparison;
- checked rejection of bad regression coefficients;
- a Lean-horizon row for general statistical regression theory.

## Concepts

- `field_statistics`
- `field_linear_algebra`
- `field_optimization_and_convexity`
- `curriculum_rationals`
- `curriculum_linear_algebra`
- `curriculum_reals`

## Trust Story

The validator parses the design matrix, response vector, coefficients, fitted
values, residuals, normal equations, and residual sums of squares as exact
rational strings. It recomputes every matrix-vector product and dot product
without floating point.

This is a finite deterministic regression replay pack. It does not claim
Gauss-Markov optimality, distributional assumptions, confidence intervals,
asymptotics, or model-selection theory.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/least-squares-regression-v0
```
