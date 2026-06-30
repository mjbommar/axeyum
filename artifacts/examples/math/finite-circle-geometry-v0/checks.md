# Checks

| Check | Expected | Proof Status | Route |
|---|---|---|---|
| `point-on-circle-witness` | `sat` | replay-only | exact rational coordinate replay |
| `tangent-line-witness` | `sat` | replay-only | exact rational line/dot-product replay |
| `chord-midpoint-perpendicular-witness` | `sat` | replay-only | exact rational midpoint/perpendicular replay |
| `bad-circle-radius-rejected` | `unsat` | checked | QF_LRA/Farkas |
| `general-circle-geometry-lean-horizon` | `not-run` | lean-horizon | Lean horizon |
