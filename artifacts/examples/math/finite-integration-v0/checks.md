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
weighted sum is `5/2`.

Proof route: finite-model replay. This row checks the finite expectation
computation; the separate `qf-lra-bad-expectation` row owns the proof-object
refutation.

## `qf-lra-bad-expectation`

Expected result: `unsat`.

The source artifact keeps the replay boundary explicit: it only asks QF_LRA to
refute the fixed equalities `integral_value = 5/2` and `integral_value = 3`.

Proof route: checked QF_LRA/Farkas evidence. The expectation computation is
finite replay; the trusted certificate checks the final linear contradiction.

## `lebesgue-integration-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove general integration theorems. Lebesgue
integration, monotone convergence, dominated convergence, Fubini/Tonelli, and
almost-everywhere reasoning need a future Lean artifact with no `sorryAx`
dependencies.
