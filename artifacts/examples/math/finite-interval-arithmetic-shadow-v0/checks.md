# Checks

| Check | Expected | Evidence Status | Trust Story |
|---|---|---|---|
| `interval-shape-witness` | `sat` | replay-only | Recompute closed interval ordering and widths. |
| `interval-sum-witness` | `sat` | replay-only | Recompute interval addition endpoints. |
| `interval-product-witness` | `sat` | replay-only | Recompute positive interval product endpoints. |
| `interval-width-witness` | `sat` | replay-only | Recompute sum/product widths and the second-order excess. |
| `bad-product-upper-rejected` | `unsat` | replay-only | Reject the false product upper bound after exact interval replay. |
| `qf-lra-bad-interval-product-upper` | `unsat` | checked | Parse the source SMT-LIB artifact, emit `UnsatFarkas`, and independently recheck it. |
| `general-interval-arithmetic-lean-horizon` | `not-run` | Lean horizon | General interval arithmetic and floating-point outward rounding are outside this fixed rational row. |

The checked row is a compact exact-rational Farkas seed. It does not certify a
floating-point interval implementation.
