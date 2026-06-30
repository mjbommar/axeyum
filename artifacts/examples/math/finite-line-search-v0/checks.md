# Checks

| Check | Expected | Evidence |
|---|---|---|
| `descent-direction-replay` | `sat` | replay-only |
| `armijo-rejection-replay` | `sat` | replay-only |
| `armijo-acceptance-replay` | `sat` | replay-only |
| `bad-armijo-acceptance-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-line-search-convergence-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only the listed rational quadratic line-search instance.
The bad row keeps the replayed Armijo violation fixed and checks a tiny linear
contradiction.
