# Checks

| Check | Expected | Proof Status | Route |
|---|---|---|---|
| `smoothstep-hermite-witness` | `sat` | replay-only | exact rational Hermite replay |
| `quadratic-unit-interval-hermite-witness` | `sat` | replay-only | exact rational Hermite replay |
| `quadratic-nonunit-interval-hermite-witness` | `sat` | replay-only | exact rational Hermite replay |
| `bad-hermite-value-rejected` | `unsat` | replay-only | exact rational bad-value replay |
| `qf-lra-bad-hermite-value` | `unsat` | checked | QF_LRA/Farkas |
| `general-hermite-interpolation-theory-lean-horizon` | `not-run` | lean-horizon | theorem boundary |

The checked row isolates the contradiction:

```text
hermite_value = 7/4
hermite_value = 2
```

The theorem-horizon row keeps interpolation uniqueness, error estimates, spline
theory, monotonicity, shape preservation, and floating-point claims out of the
finite replay surface until those routes exist.
