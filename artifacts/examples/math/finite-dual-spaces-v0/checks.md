# Checks

| Check | Result | Evidence |
|---|---|---|
| `dual-space-table-replay` | `sat` | Check covector linearity and pointwise dual operations by enumeration. |
| `dual-basis-pairing-replay` | `sat` | Recompute the pairing matrix for basis vectors and dual-basis covectors. |
| `annihilator-replay` | `sat` | Recompute all covectors that vanish on `span(10)` and check dimension. |
| `transpose-map-replay` | `sat` | Check linearity of `T`, linearity of `T*`, and `(T*phi)(v) = phi(Tv)`. |
| `bad-covector-rejected` | `unsat` | Reject a function that fails additivity on `10 + 01` with checked QF_UF/Alethe evidence. |
| `general-duality-theory-lean-horizon` | `not-run` | Names the Lean route for general duality and functional analysis. |

The checked rows are finite table replay rows, not general dual-space theorems.
