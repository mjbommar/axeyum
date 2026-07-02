# Checks

| Check | Expected | Trust |
|---|---|---|
| `matrix-inverse-replay` | `sat` | finite replay |
| `infinity-norm-replay` | `sat` | finite replay |
| `condition-number-replay` | `sat` | finite replay |
| `perturbation-bound-replay` | `sat` | finite replay |
| `bad-condition-number-rejected` | `unsat` | finite replay |
| `qf-lra-bad-condition-number` | `unsat` | checked QF_LRA/Farkas |
| `general-conditioning-stability-lean-horizon` | `not-run` | Lean horizon |

The replay rows recompute the inverse, matrix infinity norms, condition number,
nominal solve, right-hand-side perturbation, solution perturbation, and exact
relative-error inequality.

The checked row is deliberately tiny:

```text
kappa_infinity = 6
kappa_infinity <= 5
```

The finite replay computes the equality. The malformed source row claims the
upper bound. The SMT-LIB artifact exposes only that final scalar contradiction
to the Farkas route.
