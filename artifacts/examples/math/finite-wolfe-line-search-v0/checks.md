# Checks

| Check | Expected | Evidence |
|---|---|---|
| `wolfe-descent-direction-replay` | `sat` | replay-only |
| `exact-line-minimizer-replay` | `sat` | replay-only |
| `bad-line-minimizer-rejected` | `unsat` | checked QF_LRA/Farkas |
| `wolfe-sufficient-decrease-replay` | `sat` | replay-only |
| `wolfe-curvature-replay` | `sat` | replay-only |
| `bad-wolfe-curvature-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-wolfe-line-search-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only the listed rational quadratic Wolfe instance. The
bad rows keep the replayed line minimizer and curvature violation fixed and
check tiny linear contradictions.
