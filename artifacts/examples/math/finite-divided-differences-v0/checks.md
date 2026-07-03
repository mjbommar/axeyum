# Checks

| Check | Expected | Evidence |
|---|---|---|
| `quadratic-divided-difference-table` | `sat` | exact rational replay |
| `quadratic-newton-evaluation-witness` | `sat` | exact rational replay |
| `cubic-divided-difference-table` | `sat` | exact rational replay |
| `bad-interpolation-value-rejected` | `unsat` | exact rational replay |
| `qf-lra-bad-interpolation-value` | `unsat` | checked QF_LRA/Farkas |
| `general-interpolation-theory-lean-horizon` | `not-run` | theorem horizon |

The replay-only bad row is intentionally separate from the proof-object row.
Exact replay computes the interpolation value as `10` and rejects the source
claim `9`.

The checked proof route is the source SMT-LIB artifact
[`smt2/bad-interpolation-value-farkas-conflict.smt2`](smt2/bad-interpolation-value-farkas-conflict.smt2).
The route regression parses that file and requires checked `UnsatFarkas`
evidence.
