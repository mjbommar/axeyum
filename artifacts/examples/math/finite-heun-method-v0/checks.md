# Checks

| Check | Expected | Proof Status | Trust Boundary |
|---|---|---|---|
| `heun-stage-witness` | `sat` | replay-only | Recompute predictor states, endpoint derivatives, averaged slopes, and updates exactly. |
| `heun-trace-exact-solution-witness` | `sat` | replay-only | Recompute the finite trace and compare each state with `t^2`. |
| `zero-error-table-witness` | `sat` | replay-only | Recompute absolute errors and `max_error = 0` exactly. |
| `bad-heun-step-rejected` | `unsat` | replay-only | Exact replay rejects the malformed first-step value. |
| `qf-lra-bad-heun-step` | `unsat` | checked | The source SMT-LIB row emits checked `UnsatFarkas` evidence. |
| `general-heun-rk2-theory-lean-horizon` | `not-run` | Lean horizon | General RK2 theory remains outside finite replay. |

The replay-only rows are educational and deterministic. They become
solver-reuse evidence only through the separate checked QF_LRA/Farkas row.
