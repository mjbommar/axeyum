# Checks

| Check | Expected | Evidence |
|---|---|---|
| `bdf2-history-witness` | `sat` | exact rational replay |
| `bdf2-monotone-decay-witness` | `sat` | exact rational replay |
| `bad-bdf2-step-rejected` | `unsat` | exact rational replay |
| `qf-lra-bad-bdf2-step` | `unsat` | checked QF_LRA/Farkas |
| `general-bdf2-theory-lean-horizon` | `not-run` | theorem horizon |

The replay-only bad row never claims proof-object evidence. It computes the
first BDF2 next state as `5/12` and rejects the source claim `1/3`.

The checked row isolates the scalar conflict in
[`smt2/bad-bdf2-step-farkas-conflict.smt2`](smt2/bad-bdf2-step-farkas-conflict.smt2).
