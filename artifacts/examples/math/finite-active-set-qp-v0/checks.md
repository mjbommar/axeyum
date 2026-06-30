# Checks

| Check | Expected | Trust Story |
|---|---|---|
| `unconstrained-minimizer-replay` | `sat` | Exact rational replay of unconstrained gradient, value, and active-bound violation. |
| `active-face-candidate-replay` | `sat` | Exact active-face candidate replay with `x=1` fixed and `y=1` free-coordinate solve. |
| `active-set-kkt-replay` | `sat` | Exact replay of stationarity, feasibility, nonnegative multipliers, and complementary slackness. |
| `inactive-constraint-slack-replay` | `sat` | Exact replay that `y >= 0` is inactive with positive slack and zero multiplier. |
| `bad-active-set-free-gradient-rejected` | `unsat` | Source-linked QF_LRA/Farkas rejection after replay computes free stationarity error `2`. |
| `general-active-set-method-lean-horizon` | `not-run` | Lean-horizon row for active-set finite termination, degeneracy, and convergence theory. |
