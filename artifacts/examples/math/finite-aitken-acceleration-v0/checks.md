# Checks

| Check | Expected | Evidence |
|---|---|---|
| `aitken-geometric-exact-witness` | `sat` | exact rational replay |
| `aitken-harmonic-improvement-witness` | `sat` | exact rational replay |
| `aitken-residual-improvement-witness` | `sat` | exact rational replay |
| `bad-aitken-value-rejected` | `unsat` | exact rational replay |
| `qf-lra-bad-aitken-value` | `unsat` | checked QF_LRA/Farkas |
| `general-aitken-acceleration-theory-lean-horizon` | `not-run` | theorem horizon |

The replay-only bad row never claims proof-object evidence. It computes the
geometric row's accelerated value as `1` and rejects the source claim `3/2`.

The checked row isolates the scalar conflict in
[`smt2/bad-aitken-value-farkas-conflict.smt2`](smt2/bad-aitken-value-farkas-conflict.smt2).
