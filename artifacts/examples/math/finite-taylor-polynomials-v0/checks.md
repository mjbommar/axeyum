# Checks

| Check | Expected | Proof Status | Route |
|---|---|---|---|
| `quadratic-taylor-at-one-witness` | `sat` | replay-only | exact rational Taylor replay |
| `cubic-taylor-at-zero-witness` | `sat` | replay-only | exact rational Taylor replay |
| `truncated-linearization-witness` | `sat` | replay-only | exact rational truncation replay |
| `bad-taylor-value-rejected` | `unsat` | replay-only | exact rational bad-value replay |
| `qf-lra-bad-taylor-value` | `unsat` | checked | QF_LRA/Farkas |
| `general-taylor-theory-lean-horizon` | `not-run` | lean-horizon | theorem boundary |

The checked row isolates the contradiction:

```text
taylor_value = 25/4
taylor_value = 6
```

The theorem-horizon row keeps Taylor theorem, remainder-bound, convergence,
smoothness, multivariable, and floating-point claims out of the finite replay
surface until those routes exist.
