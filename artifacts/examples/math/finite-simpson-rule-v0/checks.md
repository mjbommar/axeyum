# Checks

| Check | Expected | Evidence |
|---|---|---|
| `simpson-cubic-exact-witness` | `sat` | exact rational replay |
| `simpson-quadratic-exact-witness` | `sat` | exact rational replay |
| `bad-simpson-value-rejected` | `unsat` | exact rational replay |
| `qf-lra-bad-simpson-value` | `unsat` | checked QF_LRA/Farkas |
| `general-simpson-rule-theory-lean-horizon` | `not-run` | theorem horizon |

The replay-only bad row never claims proof-object evidence. It computes the
cubic Simpson-rule value as `4` and rejects the source claim `7/2`.

The checked row isolates the scalar conflict in
[`smt2/bad-simpson-value-farkas-conflict.smt2`](smt2/bad-simpson-value-farkas-conflict.smt2).
