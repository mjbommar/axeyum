# Checks

| Check | Expected | Evidence |
|---|---|---|
| `proximal-gradient-gradient-replay` | `sat` | replay-only |
| `proximal-trial-step-replay` | `sat` | replay-only |
| `soft-threshold-prox-replay` | `sat` | replay-only |
| `composite-decrease-replay` | `sat` | replay-only |
| `bad-proximal-point-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-proximal-gradient-convergence-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only the listed rational proximal-gradient instance. The
bad row keeps the replayed proximal optimality error fixed and checks a tiny
linear contradiction.
