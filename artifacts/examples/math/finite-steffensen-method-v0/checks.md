# Checks

| Check | Expected | Evidence |
|---|---|---|
| `steffensen-half-step-exact-witness` | `sat` | exact rational replay |
| `steffensen-third-step-exact-witness` | `sat` | exact rational replay |
| `steffensen-residual-improvement-witness` | `sat` | exact rational replay |
| `bad-steffensen-value-rejected` | `unsat` | exact rational replay |
| `qf-lra-bad-steffensen-value` | `unsat` | checked QF_LRA/Farkas |
| `general-steffensen-method-theory-lean-horizon` | `not-run` | theorem horizon |

The replay-only bad row never claims proof-object evidence. It computes the
half-step row's accelerated value as `1` and rejects the source claim `3/2`.

The checked row isolates the scalar conflict in
[`smt2/bad-steffensen-value-farkas-conflict.smt2`](smt2/bad-steffensen-value-farkas-conflict.smt2).
