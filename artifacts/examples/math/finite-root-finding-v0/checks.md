# Checks

| Check | Expected | Evidence |
|---|---|---|
| `bisection-bracket-replay` | `sat` | replay-only |
| `newton-step-replay` | `sat` | replay-only |
| `residual-decrease-witness` | `sat` | replay-only |
| `bad-newton-step-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-root-finding-convergence-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only fixed rational algorithm states. The bad row keeps
the replay result fixed and checks a tiny linear contradiction.
