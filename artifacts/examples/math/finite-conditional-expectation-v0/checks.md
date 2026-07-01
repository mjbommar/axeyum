# Checks

## `conditional-expectation-partition-witness`

Expected result: `sat`.

The validator checks that the conditioning family is a partition and recomputes
each conditional expectation as a blockwise weighted average.

## `law-total-expectation-witness`

Expected result: `sat`.

The validator recomputes `E[X]` and `E[E[X | G]]` exactly and checks that the
two rational values match.

## `bad-total-expectation-rejected`

Expected result: `unsat`.

The validator rejects the claimed total-expectation row because exact replay
computes both `E[X]` and `E[E[X | G]]` as `7/2`, not `4`.

The source-linked Axeyum regression checks the final scalar contradiction as
`QF_LRA`: `source_expectation = 7/2`,
`conditional_expectation_expectation = source_expectation`, and
`conditional_expectation_expectation = 4`, requiring rechecked
`UnsatFarkas` evidence.

## `tower-property-witness`

Expected result: `sat`.

The validator checks that the fine partition refines the coarse partition and
then verifies `E[E[X | G] | H] = E[X | H]` for the listed nested partitions.

## `conditional-variance-decomposition-witness`

Expected result: `sat`.

The validator recomputes `E[X]`, `E[X^2]`, `Var(X)`, blockwise
`Var(X | G)`, `E[Var(X | G)]`, and `Var(E[X | G])` exactly, then checks the
finite decomposition `Var(X) = E[Var(X | G)] + Var(E[X | G])`.

## `bad-conditional-expectation-rejected`

Expected result: `unsat`.

The validator rejects the claimed conditional-expectation table because the
high block average is `6`, not `5`.

The resource-backed Axeyum regression checks the denominator-cleared
conditional-expectation contradiction as `QF_LRA`:
`(1/2)*high_block_expectation = 3` and
`high_block_expectation = 5`, requiring rechecked `UnsatFarkas` evidence.

## `bad-tower-property-rejected`

Expected result: `unsat`.

The validator rejects the claimed tower-property table because exact
nested-partition replay computes `E[E[X|G]|H] = 7/2` on the coarse block, not
`4`.

The source-linked Axeyum regression checks the final scalar tower contradiction
as `QF_LRA`: `tower_value = 7/2` and `tower_value = 4`, requiring rechecked
`UnsatFarkas` evidence.

## `bad-variance-decomposition-rejected`

Expected result: `unsat`.

The validator rejects the claimed variance-decomposition row because exact
finite replay computes `Var(X) = 35/4`, `E[Var(X | G)] = 5/2`, and
`Var(E[X | G]) = 25/4`, not total variance `9`.

The source-linked Axeyum regression checks the final scalar decomposition
contradiction as `QF_LRA`: `total_variance = 35/4`,
`expected_conditional_variance = 5/2`,
`conditional_mean_variance = 25/4`,
`total_variance = expected_conditional_variance + conditional_mean_variance`,
and `total_variance = 9`, requiring rechecked `UnsatFarkas` evidence.

## `general-conditional-expectation-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove the Radon-Nikodym construction, general
conditional expectation, martingales, stopping-time theorems, or regular
conditional probabilities. Those require future Lean artifacts with no
`sorryAx` dependencies.
