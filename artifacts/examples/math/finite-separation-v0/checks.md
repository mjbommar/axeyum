# Checks

| Check | Expected | Evidence |
|---|---|---|
| `convex-combination-replay` | `sat` | replay-only |
| `separating-hyperplane-replay` | `sat` | replay-only |
| `supporting-face-replay` | `sat` | replay-only |
| `bad-separator-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-separation-theorem-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only the listed finite rational points and separator.
The bad row keeps the replayed outside score fixed and checks a tiny linear
contradiction.
