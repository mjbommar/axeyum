# Checks

| Check | Expected | Evidence |
|---|---|---|
| `secant-first-step-replay` | `sat` | exact rational replay |
| `secant-second-step-replay` | `sat` | exact rational replay |
| `secant-residual-decrease-witness` | `sat` | exact rational replay |
| `bad-secant-step-rejected` | `unsat` | exact rational replay |
| `qf-lra-bad-secant-step` | `unsat` | checked QF_LRA/Farkas |
| `general-secant-method-theory-lean-horizon` | `not-run` | theorem horizon |

The replay-only bad row never claims proof-object evidence. It computes the
first secant step as `4/3` and rejects the source claim `3/2`.

The checked row isolates the scalar conflict in
[`smt2/bad-secant-step-farkas-conflict.smt2`](smt2/bad-secant-step-farkas-conflict.smt2).
