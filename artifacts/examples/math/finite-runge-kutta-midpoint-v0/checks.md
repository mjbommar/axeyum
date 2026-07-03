# Checks

| Check | Expected | Evidence Status | Purpose |
|---|---|---|---|
| `midpoint-stage-witness` | `sat` | replay-only | Recompute `k1`, midpoint time/state, and `k2`. |
| `midpoint-trace-exact-solution-witness` | `sat` | replay-only | Recompute all `y_(n+1)` updates and compare listed states with `t^2`. |
| `zero-error-table-witness` | `sat` | replay-only | Recompute absolute errors and `max_error = 0`. |
| `bad-rk-midpoint-step-rejected` | `unsat` | replay-only | Reject the malformed first next-state claim `1/2` after replay computes `1/4`. |
| `qf-lra-bad-rk-midpoint-step` | `unsat` | checked | Check the isolated scalar contradiction through QF_LRA/Farkas evidence. |
| `general-runge-kutta-theory-lean-horizon` | `not-run` | Lean horizon | Keep order, convergence, stability, stiffness, adaptivity, and floating-point claims out of the finite row. |

Validation commands:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-runge-kutta-midpoint-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_runge_kutta_midpoint_bad_step_artifact_emits_checked_farkas
```
