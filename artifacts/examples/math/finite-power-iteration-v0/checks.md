# Checks

| Check | Expected | Evidence |
|---|---|---|
| `first-power-step-replay` | `sat` | exact rational replay |
| `second-power-step-replay` | `sat` | exact rational replay |
| `normalized-iterate-replay` | `sat` | exact rational replay |
| `rayleigh-quotient-replay` | `sat` | exact rational replay |
| `residual-shadow-replay` | `sat` | exact rational replay |
| `dominant-eigenpair-shadow-replay` | `sat` | exact rational replay |
| `bad-power-iterate-coordinate-rejected` | `unsat` | replay-only false source row |
| `qf-lra-bad-power-iterate-coordinate` | `unsat` | checked `QF_LRA` / Farkas |
| `general-power-iteration-theory-lean-horizon` | `not-run` | Lean horizon |

The replay-only bad row records the source-level arithmetic failure:

```text
computed second iterate x0 = 4
claimed second iterate x0 = 3
```

The checked `QF_LRA` row isolates that final scalar contradiction in
`smt2/bad-power-iterate-coordinate-farkas-conflict.smt2`, and the solver
regression requires `Evidence::UnsatFarkas` plus independent certificate
checking.
