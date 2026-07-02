# Checks

## `pushforward-distribution-witness`

Expected result: `sat`.

The validator recomputes the pushforward distribution of a finite random
variable by summing the probabilities of all atoms mapped to each outcome.

## `expectation-through-pushforward-witness`

Expected result: `sat`.

The validator checks that expectation computed from the source atoms matches
expectation computed from the pushforward distribution.

## `independent-random-variables-witness`

Expected result: `sat`.

The validator recomputes the joint distribution of two finite random variables,
their two marginals, and checks `P(X = x and Y = y) = P(X = x) * P(Y = y)` for
every listed outcome pair.

## `bad-pushforward-rejected`

Expected result: `unsat`.

The validator rejects the claimed pushforward distribution because the exact
mass for `long` is `1/4`, not `1/2`.

Proof route: finite-model replay. This row checks the finite pushforward
computation; the separate `qf-lra-bad-pushforward` row owns the proof-object
refutation.

## `qf-lra-bad-pushforward`

Expected result: `unsat`.

The source artifact keeps the replay boundary explicit: it only asks QF_LRA to
refute the fixed equalities `long_probability = 1/4` and
`long_probability = 1/2`.

Proof route: checked QF_LRA/Farkas evidence. The pushforward computation is
finite replay; the trusted certificate checks the final linear contradiction.

## `bad-expectation-through-pushforward-rejected`

Expected result: `unsat`.

The validator rejects the claimed expectation because exact replay computes
`E[X] = 20` from both the source atom table and the pushforward distribution,
not `25`.

Proof route: finite-model replay. This row checks the finite expectation
computation; the separate `qf-lra-bad-expectation-through-pushforward` row owns
the proof-object refutation.

## `qf-lra-bad-expectation-through-pushforward`

Expected result: `unsat`.

The source artifact keeps the replay boundary explicit: it only asks QF_LRA to
refute the fixed equalities `expectation_value = 20` and
`expectation_value = 25`.

Proof route: checked QF_LRA/Farkas evidence. The expectation computation is
finite replay; the trusted certificate checks the final linear contradiction.

## `general-random-variable-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove general measurable-function theory, conditional
expectation, stochastic kernels, martingales, or continuous random variables.
Those require future Lean artifacts with no `sorryAx` dependencies.
