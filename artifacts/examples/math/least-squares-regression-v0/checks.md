# Checks

## `perfect-line-normal-equations`

Expected result: `sat`.

The validator checks a three-row design matrix, response vector, coefficient
vector, fitted values, zero residuals, `X^T X`, `X^T y`, and the normal
equations exactly.

## `least-squares-residual-orthogonality`

Expected result: `sat`.

The validator recomputes the non-perfect fit with coefficients
`(5/6, 3/2)`, checks the residual vector, verifies `X^T r = 0`, and checks
the residual sum of squares `1/6`.

## `mean-baseline-rss-comparison`

Expected result: `sat`.

The validator checks the mean-only baseline for the same response vector,
recomputes baseline residuals, and verifies that the least-squares model
improves residual sum of squares by `9/2`.

## `bad-regression-coefficients-rejected`

Expected result: `unsat`.

The validator rejects the claim that coefficients `(1, 1)` solve the same
least-squares problem because their normal-equation residual is `(1, 2)`.

The resource-backed Axeyum regression checks the first failed normal equation
as `QF_LRA`: `beta0 = 1`, `beta1 = 1`, and
`3*beta0 + 3*beta1 = 7`, requiring rechecked `UnsatFarkas` evidence.

## `general-regression-statistics-lean-horizon`

Expected result: `not-run`.

Gauss-Markov optimality, statistical inference, asymptotics, and model
selection belong in future Lean or numerical-honesty resources. The finite rows
above are exact replay checks only.
