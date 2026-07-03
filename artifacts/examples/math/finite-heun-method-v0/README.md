# Finite Heun Method Checks

Audience: learners, numerical-method authors, and solver/proof contributors who
need a tiny exact-rational two-stage time-stepping example.

This pack checks one explicit trapezoidal Runge-Kutta method, often called
Heun's method, on the fixed ODE:

```text
y' = 2t
y(0) = 0
h = 1/2
```

The exact solution is `y(t) = t^2`, so the listed finite trace lands exactly on
the solution at `0`, `1/2`, `1`, and `3/2`. The trusted part is exact rational
replay of the predictor stage, endpoint derivative, averaged slope, finite
error table, and a checked QF_LRA/Farkas contradiction for one malformed first
step.

## What This Pack Checks

- Predictor-stage replay for Heun's method.
- Endpoint-slope and averaged-slope replay.
- Exact finite trace comparison against `y = t^2`.
- A zero finite error table on the listed grid.
- Rejection of the malformed first-step claim `next_state = 1/2` when exact
  replay computes `1/4`.
- A source-linked QF_LRA/Farkas proof row for that scalar contradiction.

## What This Pack Does Not Prove

This pack does not prove general Runge-Kutta order conditions, global
convergence, stability regions, A-stability, stiff-system behavior, adaptive
step-size correctness, floating-point correctness, or PDE time-integration
theory. Those remain Lean/theorem or numerical-honesty work.

## Files

- `metadata.json` records concept links, fields, fragments, solver-reuse
  disposition, and graduation criteria.
- `expected.json` records the witness trace and expected check rows.
- `model.md` explains the finite transition model.
- `checks.md` summarizes the trust boundary for each row.
- `smt2/bad-heun-step-farkas-conflict.smt2` is the source linear contradiction
  used by the Farkas regression.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-heun-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_heun_bad_step_artifact_emits_checked_farkas
```
