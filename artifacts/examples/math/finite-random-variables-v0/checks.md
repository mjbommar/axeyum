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
mass for `long` is `1/4`, not `1/2`. The source-linked QF_LRA artifact records
the final exact-linear contradiction checked by the shared Farkas route
regression.

## `bad-expectation-through-pushforward-rejected`

Expected result: `unsat`.

The validator rejects the claimed expectation because exact replay computes
`E[X] = 20` from both the source atom table and the pushforward distribution,
not `25`. The source-linked QF_LRA artifact records the final exact-linear
contradiction checked by the shared Farkas route regression.

## `general-random-variable-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove general measurable-function theory, conditional
expectation, stochastic kernels, martingales, or continuous random variables.
Those require future Lean artifacts with no `sorryAx` dependencies.
