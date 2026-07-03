# Finite Adams-Bashforth Method Checks

Audience: learners, numerical-method authors, and solver/proof contributors who
need a tiny exact-rational linear multistep time-stepping example.

This pack checks one two-step Adams-Bashforth trace on the fixed ODE:

```text
y' = 2t
y(0) = 0
h = 1/2
starter y_1 = 1/4
```

The two-step Adams-Bashforth method uses derivative history:

```text
y_(n+1) = y_n + h * ((3/2)*f(t_n,y_n) - (1/2)*f(t_(n-1),y_(n-1)))
```

For `f(t, y) = 2t`, the derivative history is linear in time, so the listed
finite trace lands exactly on `y = t^2`. The trusted part is exact rational
replay of the starter value, derivative history, Adams-Bashforth slopes,
finite zero-error table, and a checked QF_LRA/Farkas contradiction for one
malformed multistep update.

## What This Pack Checks

- Exact starter-value replay for `y_1 = 1/4`.
- Derivative-history replay for `f(t,y) = 2t`.
- Exact AB2 slope replay for the two listed multistep updates.
- Rejection of the malformed first multistep claim `next_state = 3/4` when
  exact replay computes `1`.
- A source-linked QF_LRA/Farkas proof row for that scalar contradiction.

## What This Pack Does Not Prove

This pack does not prove general Adams-Bashforth order, consistency,
zero-stability, convergence, variable-step correctness, history-initialization
theory, floating-point correctness, or PDE method-of-lines behavior. Those
remain Lean/theorem or numerical-honesty work.

## Files

- `metadata.json` records concept links, fields, fragments, solver-reuse
  disposition, and graduation criteria.
- `expected.json` records the witness trace and expected check rows.
- `model.md` explains the finite multistep model.
- `checks.md` summarizes the trust boundary for each row.
- `smt2/bad-adams-bashforth-step-farkas-conflict.smt2` is the source linear
  contradiction used by the Farkas regression.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-adams-bashforth-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_adams_bashforth_bad_step_artifact_emits_checked_farkas
```
