# Checks

| Check | Expected | Trust Story |
|---|---:|---|
| `pivot-multiplier-replay` | `sat` | Replay computes the pivot and row multiplier exactly. |
| `row-operation-replay` | `sat` | Replay applies the row replacement to the augmented matrix. |
| `determinant-pivot-product-replay` | `sat` | Replay checks `det(A) = 6` and pivot product `2 * 3 = 6`. |
| `back-substitution-replay` | `sat` | Replay solves the triangular system and checks `A*x = b`. |
| `bad-eliminated-rhs-rejected` | `unsat` | Exact replay rejects the malformed source claim `7 = 8`. |
| `qf-lra-bad-eliminated-rhs` | `unsat` | Source SMT-LIB artifact emits checked `UnsatFarkas` evidence. |
| `general-gaussian-elimination-theory-lean-horizon` | `not-run` | Pivoting correctness, rank-revealing variants, and stability require future theorem/numerical-honesty work. |

The replay rows are source-level arithmetic checks. The checked row deliberately
isolates a tiny scalar contradiction so the Farkas route can be tested without
pretending that one finite transcript proves the general elimination algorithm.
