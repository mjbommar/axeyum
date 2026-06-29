# Checks

## `first-hit-distribution-witness`

Expected result: `sat`.

The validator computes first-hit probabilities up to the finite horizon by
zeroing target-state mass after each step and carrying only not-yet-hit mass
forward.

## `absorption-probability-equations`

Expected result: `sat`.

The validator checks the finite absorption-probability fixed-point equations:
target states have probability `1`, and non-target states equal the transition
weighted average of successor probabilities.

## `expected-hitting-time-equations`

Expected result: `sat`.

The validator checks the finite expected hitting-time equations: target states
have time `0`, and non-target states satisfy `h(i) = 1 + sum_j P(i,j) h(j)`.

## `bad-expected-time-rejected`

Expected result: `unsat`.

The validator rejects the malformed expected-time table because the equation at
`start` evaluates to `7/2`, not the claimed `3`.

## `general-hitting-theory-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove recurrence/transience classifications,
infinite-horizon convergence, mixing bounds, optional stopping, or potential
theory for general Markov chains. Those require future Lean artifacts with no
`sorryAx` dependencies.
