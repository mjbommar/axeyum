# Checks

| Check | Expected | Trust |
|---|---|---|
| `quadratic-gradient-hessian-replay` | `sat` | finite replay |
| `newton-linear-solve-replay` | `sat` | finite replay |
| `newton-step-stationarity-replay` | `sat` | finite replay |
| `newton-objective-decrease-replay` | `sat` | finite replay |
| `bad-newton-coordinate-rejected` | `unsat` | finite replay |
| `qf-lra-bad-newton-coordinate` | `unsat` | checked QF_LRA/Farkas |
| `general-newton-method-lean-horizon` | `not-run` | Lean horizon |

The replay rows recompute the fixed polynomial value, gradient, Hessian,
Newton right-hand side, exact linear solve, next point, stationarity, and
objective decrease.

The checked row is deliberately tiny:

```text
newton_next_x = 10/7
newton_next_x = 3/2
```

The finite replay computes the first equality. The malformed source row claims
the second equality. The SMT-LIB artifact exposes only that final scalar
conflict to the Farkas route.
