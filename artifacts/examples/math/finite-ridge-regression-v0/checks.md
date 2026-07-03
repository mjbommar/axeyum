# Checks

## `ridge-normal-equations-witness`

Expected result: `sat`.

The validator recomputes `X^T X`, `X^T y`, `X^T X + lambda I`, fitted values,
residuals, RSS, coefficient penalty, objective value, and the regularized
normal equations exactly.

## `ridge-shrinkage-witness`

Expected result: `sat`.

The validator compares the ridge coefficient norm `101/45` with the
ordinary least-squares coefficient norm `53/18` for the adjacent finite
dataset. This is a fixed exact shrinkage witness, not a general theorem.

## `ridge-objective-comparison-witness`

Expected result: `sat`.

The validator checks that the ridge coefficients have regularized objective
`41/15`, while the ordinary least-squares coefficients have regularized
objective `28/9`, giving the exact improvement `17/45`.

## `bad-ridge-beta0-rejected`

Expected result: `unsat`.

The validator rejects the claim that the first ridge coefficient is `1`.
Exact replay computes `beta0 = 4/5`.

## `qf-lra-bad-ridge-beta0`

Expected result: `unsat`.

The resource-backed Axeyum regression checks the final linear conflict as
`QF_LRA`: the regularized normal equations plus `beta0 = 1`, requiring
rechecked `UnsatFarkas` evidence.

## `general-ridge-regression-theory-lean-horizon`

Expected result: `not-run`.

General ridge optimality, estimator bias/variance tradeoffs, regularization
path theory, cross-validation, model selection, floating-point solvers, and
numerical stability belong in future Lean or numerical-honesty resources.
The finite rows above are exact replay checks only.
