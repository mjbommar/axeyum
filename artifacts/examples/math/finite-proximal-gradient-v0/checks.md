# Checks

| Check | Expected | Evidence |
|---|---|---|
| `proximal-gradient-gradient-replay` | `sat` | replay-only |
| `proximal-trial-step-replay` | `sat` | replay-only |
| `soft-threshold-prox-replay` | `sat` | replay-only |
| `composite-decrease-replay` | `sat` | replay-only |
| `bad-composite-decrease-rejected` | `unsat` | checked QF_LRA/Farkas |
| `box-plus-l1-prox-replay` | `sat` | replay-only |
| `bad-proximal-point-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-box-proximal-point-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-proximal-gradient-convergence-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only the listed rational proximal-gradient instance. The
bad rows keep the replayed proximal optimality error, composite-decrease error,
or box-feasibility violation fixed and check tiny linear contradictions.
