# Checks

## `conditional-expectation-partition-witness`

Expected result: `sat`.

The validator checks that the conditioning family is a partition and recomputes
each conditional expectation as a blockwise weighted average.

## `law-total-expectation-witness`

Expected result: `sat`.

The validator recomputes `E[X]` and `E[E[X | G]]` exactly and checks that the
two rational values match.

## `tower-property-witness`

Expected result: `sat`.

The validator checks that the fine partition refines the coarse partition and
then verifies `E[E[X | G] | H] = E[X | H]` for the listed nested partitions.

## `bad-conditional-expectation-rejected`

Expected result: `unsat`.

The validator rejects the claimed conditional-expectation table because the
high block average is `6`, not `5`.

The resource-backed Axeyum regression checks the denominator-cleared
conditional-expectation contradiction as `QF_LRA`:
`(1/2)*high_block_expectation = 3` and
`high_block_expectation = 5`, requiring rechecked `UnsatFarkas` evidence.

## `general-conditional-expectation-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove the Radon-Nikodym construction, general
conditional expectation, martingales, stopping-time theorems, or regular
conditional probabilities. Those require future Lean artifacts with no
`sorryAx` dependencies.
