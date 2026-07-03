# Checks

| Check | Expected | Evidence |
|---|---|---|
| `romberg-quadratic-exact-witness` | `sat` | exact rational replay |
| `romberg-quadratic-error-cancellation-witness` | `sat` | exact rational replay |
| `romberg-quartic-error-witness` | `sat` | exact rational replay |
| `bad-romberg-value-rejected` | `unsat` | exact rational replay |
| `qf-lra-bad-romberg-value` | `unsat` | checked QF_LRA/Farkas |
| `general-romberg-extrapolation-theory-lean-horizon` | `not-run` | theorem horizon |

The replay-only bad row never claims proof-object evidence. It computes the
quadratic Romberg value as `1/3` and rejects the source claim `1/4`.

The checked row isolates the scalar conflict in
[`smt2/bad-romberg-value-farkas-conflict.smt2`](smt2/bad-romberg-value-farkas-conflict.smt2).
