# Checks

| Check | Expected | Evidence |
|---|---|---|
| `wolfe-descent-direction-replay` | `sat` | replay-only |
| `exact-line-minimizer-replay` | `sat` | replay-only |
| `wolfe-sufficient-decrease-replay` | `sat` | replay-only |
| `wolfe-curvature-replay` | `sat` | replay-only |
| `bad-wolfe-curvature-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-wolfe-line-search-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only the listed rational quadratic Wolfe instance. The
bad row keeps the replayed curvature violation fixed and checks a tiny linear
contradiction.
