# Finite Euler Method V0

This pack extends the `differential_equations_and_dynamical_systems` and
`numerical_analysis` field rows with exact finite Euler-method checks. It treats
an ODE stepper as a bounded rational transition system, not as a complete
continuous-time theorem.

The pack covers:

- explicit Euler replay for the linear decay equation `y' = -y`;
- exact finite error replay for Euler on `y' = 2t` with solution `y = t^2`;
- a nonnegative monotone invariant over a finite Euler trace;
- checked QF_LRA/Farkas rejection of a bad finite error bound;
- checked QF_LRA/Farkas rejection of a bad terminal error;
- checked QF_LRA/Farkas rejection of a bad Euler update;
- a Lean-horizon row for continuous-time ODE theory and convergence theorems.

## Concepts

- `field_differential_equations_and_dynamical_systems`
- `field_numerical_analysis`
- `field_real_analysis`
- `curriculum_calculus`
- `curriculum_sequences_and_limits`
- `curriculum_reals`

## Trust Story

The validator parses step sizes, time grids, states, derivatives, exact
solutions, and errors as exact rational strings. It recomputes every Euler
update and every listed error without floating point. The false error-bound and
terminal-error rows, plus the false fixed-step row, are routed through Axeyum's
checked `UnsatFarkas` evidence path.

This is a finite replay pack. It does not prove existence/uniqueness,
stability, global convergence rates, stiffness behavior, or PDE theory.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-euler-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_euler_bad_
```
