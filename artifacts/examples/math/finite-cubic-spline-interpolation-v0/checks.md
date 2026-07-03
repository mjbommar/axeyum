# Checks

| Check | Expected | Proof Status | Route |
|---|---|---|---|
| `natural-spline-left-midpoint-witness` | `sat` | replay-only | exact rational natural spline replay |
| `natural-spline-right-midpoint-witness` | `sat` | replay-only | exact rational natural spline replay |
| `natural-spline-knot-smoothness-witness` | `sat` | replay-only | exact rational natural spline replay |
| `bad-spline-value-rejected` | `unsat` | replay-only | exact rational bad-value replay |
| `qf-lra-bad-spline-value` | `unsat` | checked | QF_LRA/Farkas |
| `general-spline-interpolation-theory-lean-horizon` | `not-run` | lean-horizon | theorem boundary |

The checked QF_LRA row isolates the exact scalar conflict:

```text
spline_value = 11/16
spline_value = 3/4
```

The broader spline theory claims remain outside this pack.
