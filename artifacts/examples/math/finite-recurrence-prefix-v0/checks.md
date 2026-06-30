# Checks

| Check | Expected | Evidence |
|---|---|---|
| `fibonacci-prefix-replay` | `sat` | replay-only |
| `affine-recurrence-prefix-replay` | `sat` | replay-only |
| `companion-matrix-prefix-replay` | `sat` | replay-only |
| `bad-fibonacci-value-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-recurrence-theory-lean-horizon` | `not-run` | Lean horizon |

The replay rows are finite list checks. The bad row keeps the replay result
fixed and asks Axeyum to produce independently checked evidence for the tiny
linear contradiction.
