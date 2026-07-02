# Checks

| Check | Expected | Evidence |
|---|---|---|
| `bisection-bracket-replay` | `sat` | replay-only |
| `newton-step-replay` | `sat` | replay-only |
| `residual-decrease-witness` | `sat` | replay-only |
| `bad-newton-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-newton-step` | `unsat` | checked QF_LRA/Farkas |
| `bad-bisection-width-rejected` | `unsat` | replay-only |
| `qf-lra-bad-bisection-width` | `unsat` | checked QF_LRA/Farkas |
| `general-root-finding-convergence-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only fixed rational algorithm states. The bad source rows
compute the malformed values exactly; the separate `qf-lra-*` rows check the
tiny linear contradictions.
