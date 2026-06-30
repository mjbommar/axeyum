# Checks

| Check | Expected | Evidence |
|---|---|---|
| `cyclic-quadrilateral-witness` | `sat` | exact rational replay |
| `cyclic-diagonal-intersection-witness` | `sat` | exact midpoint and dot-product replay |
| `cyclic-opposite-right-angles-witness` | `sat` | exact angle-vector replay |
| `bad-cyclic-diagonal-intersection-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-cyclic-geometry-lean-horizon` | `not-run` | Lean horizon |
