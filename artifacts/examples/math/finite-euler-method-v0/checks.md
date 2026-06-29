# Checks

## `linear-decay-euler-trace`

Expected result: `sat`.

The validator checks the time grid and every update for explicit Euler on
`y' = -y` with step size `1/2`, starting from `y(0) = 1`.

## `quadratic-forcing-error-replay`

Expected result: `sat`.

The validator checks Euler replay for `y' = 2t`, recomputes the exact
polynomial solution `t^2` on the grid, and verifies the listed absolute errors.

## `nonnegative-monotone-invariant`

Expected result: `sat`.

The validator checks that the finite linear-decay Euler trace remains inside
`[0, 1]` and is monotone nonincreasing.

## `bad-euler-step-rejected`

Expected result: `unsat`.

The validator rejects the false one-step claim for `y' = -y`: from `y = 1`
with step `1/2`, explicit Euler gives `1/2`, not `3/4`.

## `general-ode-theory-lean-horizon`

Expected result: `not-run`.

Continuous-time ODE existence, uniqueness, stability, convergence, stiffness,
and PDE theory belong in future Lean or numerical-honesty resources. The finite
rows above are exact replay checks only.
