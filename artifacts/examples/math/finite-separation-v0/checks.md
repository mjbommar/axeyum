# Checks

| Check | Expected | Evidence |
|---|---|---|
| `convex-combination-replay` | `sat` | replay-only |
| `separating-hyperplane-replay` | `sat` | replay-only |
| `supporting-face-replay` | `sat` | replay-only |
| `bad-convex-combination-point-rejected` | `unsat` | replay-only |
| `qf-lra-bad-convex-combination-point` | `unsat` | checked QF_LRA/Farkas |
| `bad-separator-rejected` | `unsat` | replay-only |
| `qf-lra-bad-separator` | `unsat` | checked QF_LRA/Farkas |
| `general-separation-theorem-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only the listed finite rational points and separator.
The bad source rows keep replayed values fixed; the separate `qf-lra-*` rows
check the tiny linear contradictions.
