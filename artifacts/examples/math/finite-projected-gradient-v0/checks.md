# Checks

| Check | Expected | Evidence |
|---|---|---|
| `projected-gradient-gradient-replay` | `sat` | replay-only |
| `unconstrained-step-replay` | `sat` | replay-only |
| `interval-projection-replay` | `sat` | replay-only |
| `projected-descent-replay` | `sat` | replay-only |
| `bad-projected-point-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-projected-decrease-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-projected-gradient-convergence-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only the listed rational quadratic projected-gradient
instance. The bad rows keep the malformed projected point or projected-decrease
claim fixed and check tiny linear contradictions.
