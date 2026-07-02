# Checks

| Check | Expected | Evidence |
|---|---|---|
| `initial-residual-replay` | `sat` | exact rational replay |
| `first-cg-step-replay` | `sat` | exact rational replay |
| `residual-orthogonality-replay` | `sat` | exact rational replay |
| `beta-direction-replay` | `sat` | exact rational replay |
| `search-direction-conjugacy-replay` | `sat` | exact rational replay |
| `second-step-solution-replay` | `sat` | exact rational replay |
| `bad-cg-alpha0-rejected` | `unsat` | replay-only false source row |
| `qf-lra-bad-cg-alpha0` | `unsat` | checked `QF_LRA` / Farkas |
| `general-conjugate-gradient-theory-lean-horizon` | `not-run` | Lean horizon |

The replay-only bad row records the source-level arithmetic failure:

```text
computed alpha0 = 1/4
claimed alpha0 = 1/3
```

The checked `QF_LRA` row isolates that final scalar contradiction in
`smt2/bad-cg-alpha0-farkas-conflict.smt2`, and the solver regression requires
`Evidence::UnsatFarkas` plus independent certificate checking.
