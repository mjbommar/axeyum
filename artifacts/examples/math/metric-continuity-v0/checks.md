# Checks

## `finite-lipschitz-witness`

Expected result: `sat`.

The validator checks every pair in the finite metric-space slice and confirms
`|f(x)-f(y)| <= 2*d(x,y)`.

## `epsilon-delta-continuity-witness`

Expected result: `sat`.

The validator recomputes the finite `delta` ball around `p0`, recomputes the
finite output `epsilon` ball around `f(p0)`, and checks containment.

## `open-ball-preimage-witness`

Expected result: `sat`.

The validator recomputes the preimage of `|y - 0| < 1` and confirms it matches
the listed domain ball.

## `bad-delta-rejected`

Expected result: `unsat`.

The validator checks the counterexample `p2`: it is within the claimed
`delta = 3/4` of `p0`, but its output is at distance `1`, not strictly less
than `epsilon = 1`.

## `general-continuity-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove general continuity over real metric spaces. That
requires a future Lean artifact with no `sorryAx` dependencies.
