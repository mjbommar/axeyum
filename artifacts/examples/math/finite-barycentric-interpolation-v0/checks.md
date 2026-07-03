# Checks

| Check | Expected | Evidence |
|---|---|---|
| `linear-barycentric-evaluation-witness` | `sat` | replay-only |
| `quadratic-barycentric-evaluation-witness` | `sat` | replay-only |
| `node-hit-barycentric-witness` | `sat` | replay-only |
| `bad-barycentric-value-rejected` | `unsat` | replay-only |
| `qf-lra-bad-barycentric-value` | `unsat` | checked QF_LRA/Farkas |
| `general-barycentric-interpolation-theory-lean-horizon` | `not-run` | Lean horizon |

Replay-only rows are deterministic exact-rational checks. The checked row is the
source-linked QF_LRA/Farkas scalar contradiction

```text
barycentric_value = 4
barycentric_value = 5
```

The horizon row prevents this finite exact resource from claiming arbitrary
interpolation uniqueness, barycentric/Lagrange/Newton equivalence,
conditioning, error bounds, Runge-phenomenon analysis, spline theory, or
floating-point interpolation correctness.
