# Checks

| Check | Expected | Evidence |
|---|---|---|
| `quadratic-gradient-replay` | `sat` | replay-only |
| `gradient-descent-step-replay` | `sat` | replay-only |
| `descent-bound-replay` | `sat` | replay-only |
| `bad-descent-value-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-step-coordinate-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-descent-bound-slack-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-gradient-descent-convergence-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only the listed rational quadratic and one exact
gradient-descent step. The bad rows keep the replayed decrease and step
coordinate or descent-bound slack fixed and check tiny linear contradictions.
