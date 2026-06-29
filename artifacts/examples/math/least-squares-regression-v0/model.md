# Model

A regression instance is represented by:

```text
X beta ~= y
```

where `X` is an exact rational design matrix, `beta` is the coefficient vector,
and `y` is the response vector. Ordinary least squares is checked through the
normal equations:

```text
X^T X beta = X^T y
```

Residuals use the convention:

```text
r = y - X beta
```

The finite optimality shadow is `X^T r = 0`.

## Perfect Line

For points `(0, 1)`, `(1, 3)`, and `(2, 5)`, the affine fit is:

```text
beta = (1, 2)
y = 1 + 2x
```

The residual vector is zero and `RSS = 0`.

## Projection Fit

For response vector `(1, 2, 4)` on the same design matrix:

```text
beta = (5/6, 3/2)
fitted = (5/6, 7/3, 23/6)
residuals = (1/6, -1/3, 1/6)
RSS = 1/6
```

The residuals are orthogonal to the intercept and slope columns.

## Mean Baseline

The mean-only baseline has mean `7/3` and residual sum of squares `14/3`. The
least-squares fit has residual sum of squares `1/6`, so the improvement is
`9/2`.

## False Coefficients

The coefficients `(1, 1)` give fitted values `(1, 2, 3)` and residuals
`(0, 0, 1)`. Their normal-equation residual is `(1, 2)`, so they do not solve
the fixed least-squares problem.

The first failed normal equation is linear:

```text
3*beta0 + 3*beta1 = 7
```

With `beta0 = beta1 = 1`, this reduces to `6 = 7`; the pack keeps that final
contradiction on the checked `UnsatFarkas` route.

These rows are exact finite replay targets, not a general regression theory.
