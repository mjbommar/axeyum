# Checks

| Check | Expected | Evidence |
|---|---|---|
| `forward-difference-affine-exact-witness` | `sat` | replay-only |
| `central-difference-quadratic-exact-witness` | `sat` | replay-only |
| `second-central-difference-quadratic-exact-witness` | `sat` | replay-only |
| `bad-finite-difference-value-rejected` | `unsat` | replay-only |
| `qf-lra-bad-finite-difference-value` | `unsat` | checked QF_LRA/Farkas |
| `general-finite-difference-theory-lean-horizon` | `not-run` | Lean horizon |

Replay-only rows are deterministic exact-rational checks. The checked row is
the source-linked QF_LRA/Farkas scalar contradiction

```text
finite_difference_value = 4
finite_difference_value = 5
```

The horizon row prevents this finite exact resource from claiming arbitrary
finite-difference exactness, truncation-error bounds, convergence order,
stability, PDE discretization correctness, automatic-differentiation behavior,
or floating-point derivative accuracy.
