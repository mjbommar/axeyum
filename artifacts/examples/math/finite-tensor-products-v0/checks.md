# Checks

| Check | Result | Evidence |
|---|---|---|
| `tensor-product-basis-replay` | `sat` | Validate finite vector-space tables, dimension product, and span of listed basis tensors. |
| `bilinear-map-table-replay` | `sat` | Exhaustively check additivity and scalar preservation in each argument. |
| `universal-factorization-replay` | `sat` | Check `gamma(v,w) = h(beta(v,w))` for every finite pair and verify `h` is linear. |
| `kronecker-product-replay` | `sat` | Recompute the 4x4 Kronecker-product matrix over `F2`. |
| `bad-bilinear-map-rejected` | `unsat` | Recompute a left-additivity counterexample with checked QF_UF/Alethe evidence. |
| `general-tensor-theory-lean-horizon` | `not-run` | Names the Lean route for full tensor and multilinear algebra. |

The checked rows are exact finite replay rows, not abstract tensor-product
theorems.
