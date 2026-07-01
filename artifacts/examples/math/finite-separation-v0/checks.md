# Checks

| Check | Expected | Evidence |
|---|---|---|
| `convex-combination-replay` | `sat` | replay-only |
| `separating-hyperplane-replay` | `sat` | replay-only |
| `supporting-face-replay` | `sat` | replay-only |
| `bad-convex-combination-point-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-separator-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-separation-theorem-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only the listed finite rational points and separator.
The bad rows keep replayed values fixed and check tiny linear contradictions.
