# Checks

| Check | Expected | Evidence Status | Trust Story |
|---|---|---|---|
| `exact-increment-replay` | `sat` | replay-only | Recompute `x + y` and `exact_sum - x` over rationals. |
| `rounding-grid-replay` | `sat` | replay-only | Recompute the three-decimal scale, scaled values, rounded grid units, and nearest-grid residuals. |
| `rounded-increment-loss-replay` | `sat` | replay-only | Recompute the rounded increment and compare it with the exact increment. |
| `bad-rounded-equals-exact-rejected` | `unsat` | replay-only | Reject the false claim that the rounded increment equals the exact increment. |
| `qf-lra-bad-rounded-equals-exact` | `unsat` | checked | Parse the source SMT-LIB artifact, emit `UnsatFarkas`, and independently recheck it. |
| `general-floating-roundoff-lean-horizon` | `not-run` | Lean horizon | IEEE floating-point semantics and general roundoff/stability theorems are outside this fixed replay row. |

The replay rows are intentionally small. The checked row is a regression seed
for the exact rational Farkas route, not evidence that Axeyum has a complete
floating-point theory.
