# Checks

| Check | Expected | Evidence |
|---|---|---|
| `bisection-bracket-replay` | `sat` | replay-only |
| `newton-step-replay` | `sat` | replay-only |
| `residual-decrease-witness` | `sat` | replay-only |
| `bad-newton-step-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-bisection-width-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-root-finding-convergence-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only fixed rational algorithm states. The bad rows keep
the replay results fixed and check tiny linear contradictions.
