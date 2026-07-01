# Checks

## `linear-decay-euler-trace`

Expected result: `sat`.

The validator checks the time grid and every update for explicit Euler on
`y' = -y` with step size `1/2`, starting from `y(0) = 1`.

## `quadratic-forcing-error-replay`

Expected result: `sat`.

The validator checks Euler replay for `y' = 2t`, recomputes the exact
polynomial solution `t^2` on the grid, and verifies the listed absolute errors.

## `bad-max-error-bound-rejected`

Expected result: `unsat`.

The validator replays the same quadratic-forcing error table and recomputes the
maximum error as `3/4`. The malformed claim says the max error is at most
`1/2`; the source QF_LRA artifact isolates `max_error = 3/4` and
`max_error <= 1/2` for Farkas checking.

## `bad-terminal-error-rejected`

Expected result: `unsat`.

The validator replays the same quadratic-forcing error table and recomputes the
terminal error as `|9/4 - 3/2| = 3/4`. The malformed claim says the terminal
error is `1/2`; the source QF_LRA artifact isolates both equalities for Farkas
checking.

## `nonnegative-monotone-invariant`

Expected result: `sat`.

The validator checks that the finite linear-decay Euler trace remains inside
`[0, 1]` and is monotone nonincreasing.

## `bad-euler-step-rejected`

Expected result: `unsat`.

The validator rejects the false one-step claim for `y' = -y`: from `y = 1`
with step `1/2`, explicit Euler gives `1/2`, not `3/4`.

The resource-backed Axeyum regression checks the transition contradiction as
`QF_LRA`: `state = 1`, `derivative = -1`,
`next_state = state + (1/2)*derivative`, and `next_state = 3/4`, requiring
rechecked `UnsatFarkas` evidence.

## `general-ode-theory-lean-horizon`

Expected result: `not-run`.

Continuous-time ODE existence, uniqueness, stability, convergence, stiffness,
and PDE theory belong in future Lean or numerical-honesty resources. The finite
rows above are exact replay checks only.
