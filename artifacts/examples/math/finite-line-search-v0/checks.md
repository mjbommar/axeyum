# Checks

| Check | Expected | Evidence |
|---|---|---|
| `descent-direction-replay` | `sat` | replay-only |
| `armijo-rejection-replay` | `sat` | replay-only |
| `armijo-acceptance-replay` | `sat` | replay-only |
| `bad-armijo-acceptance-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-accepted-candidate-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-line-search-convergence-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only the listed rational quadratic line-search instance.
The bad rows keep the replayed Armijo violation and accepted candidate fixed
and check tiny linear contradictions.
