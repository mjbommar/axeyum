# Finite Backward Euler Method Checks

Audience: learners, numerical-method authors, and solver/proof contributors who
need a tiny exact-rational implicit time-stepping example.

This pack checks one backward Euler trace on the fixed ODE:

```text
y' = -y
y(0) = 1
h = 1/2
```

Backward Euler uses the endpoint state in the derivative:

```text
y_(n+1) = y_n + h * f(t_(n+1), y_(n+1))
```

For `f(t, y) = -y` and `h = 1/2`, the implicit equation forces
`y_(n+1) = (2/3) * y_n`. The trusted part is exact rational replay of the
endpoint derivatives, implicit residuals, geometric decay ratio, and a checked
QF_LRA/Farkas contradiction for one malformed first step.

## What This Pack Checks

- Endpoint derivative replay for backward Euler.
- Exact implicit residuals for each listed transition.
- Positive monotone geometric decay with ratio `2/3` on the listed trace.
- Rejection of the malformed first-step claim `next_state = 1/2` when exact
  replay computes `2/3`.
- A source-linked QF_LRA/Farkas proof row for that scalar contradiction.

## What This Pack Does Not Prove

This pack does not prove general backward Euler convergence, A-stability,
stiff-system behavior, nonlinear solve correctness, adaptive step-size
correctness, floating-point correctness, or PDE time-integration theory. Those
remain Lean/theorem or numerical-honesty work.

## Files

- `metadata.json` records concept links, fields, fragments, solver-reuse
  disposition, and graduation criteria.
- `expected.json` records the witness trace and expected check rows.
- `model.md` explains the finite transition model.
- `checks.md` summarizes the trust boundary for each row.
- `smt2/bad-backward-euler-step-farkas-conflict.smt2` is the source linear
  contradiction used by the Farkas regression.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-backward-euler-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_backward_euler_bad_step_artifact_emits_checked_farkas
```
