# Checks

## `simple-function-integral-witness`

Expected result: `sat`.

The validator recomputes the exact rational weighted sum
`sum_x f(x) * P(x)`.

## `indicator-integral-witness`

Expected result: `sat`.

The validator recomputes the event measure and checks that the integral of the
indicator function equals that measure.

## `integral-linearity-witness`

Expected result: `sat`.

The validator recomputes `integral f`, `integral g`, the pointwise function
`2*f - g`, and the combined integral exactly.

## `bad-expectation-rejected`

Expected result: `unsat`.

The validator rejects the claimed integral `3` because the exact finite
weighted sum is `5/2`. The source-linked QF_LRA artifact records the final
exact-linear contradiction checked by the shared Farkas route regression.

## `lebesgue-integration-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove general integration theorems. Lebesgue
integration, monotone convergence, dominated convergence, Fubini/Tonelli, and
almost-everywhere reasoning need a future Lean artifact with no `sorryAx`
dependencies.
