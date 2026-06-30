# Checks

| ID | Expected | Trust Status | Route |
|---|---|---|---|
| `ordered-field-midpoint-witness` | `sat` | replay-only | Exact ordered-field midpoint replay. |
| `nra-product-threshold-witness` | `sat` | replay-only | Exact nonlinear product replay. |
| `quadratic-root-real-witness` | `sat` | replay-only | Exact polynomial evaluation at a rational real root. |
| `square-nonnegative-unsat` | `unsat` | checked | Fixed square-nonnegative certificate shape: no real has `x^2 < 0`. |
| `negative-discriminant-no-real-root` | `unsat` | checked | Quadratic discriminant check for `x^2 + 1 = 0`. |
| `negative-discriminant-farkas-conflict` | `unsat` | checked | Check the replayed discriminant `-4` against the nonnegative-discriminant requirement with QF_LRA/Farkas evidence. |
| `real-completeness-lean-horizon` | `not-run` | lean-horizon | Completeness and epsilon-delta reasoning need a proof assistant. |

The first three rows are replayed witnesses. The two UNSAT rows are tiny
algebraic certificate checks, not a general RCF implementation. The promoted
Farkas row checks only the final linear discriminant contradiction after exact
polynomial replay has computed the discriminant.
