# Finite Projected Gradient Checks

This pack turns one exact rational projected-gradient step into resource rows.
It checks only the listed quadratic, interval constraint, unconstrained step,
projection, projected descent, and false projected-point obstruction; general
projected-gradient convergence and constrained-optimization theorems remain
proof horizons.

## Audience

- Learners connecting calculus, constraints, and numerical optimization.
- Resource authors who need a small projected-gradient witness with explicit
  trust boundaries.
- Solver developers looking for exact-rational QF_LRA/Farkas rows after replay.

## Checks

- `projected-gradient-gradient-replay`: recomputes the derivative at the
  feasible start point.
- `unconstrained-step-replay`: checks the listed gradient step before
  projection.
- `interval-projection-replay`: checks projection of the trial point onto the
  closed rational interval.
- `projected-descent-replay`: recomputes objective values and projected-step
  decrease.
- `bad-projected-point-rejected`: rejects the malformed claim that `3/2` is a
  feasible projected point for the interval `[0,1]`.
- `general-projected-gradient-convergence-lean-horizon`: names the future proof
  route for projected-gradient convergence, constraint qualifications, and rate
  theorems.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-projected-gradient-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_projected_gradient_bad_projection_artifact_emits_checked_farkas
```

## Trust Boundary

Untrusted search may propose the step size, trial point, or projected point.
The trusted work is small: exact derivative replay, exact step arithmetic,
exact interval projection, exact objective evaluation, and checked
`UnsatFarkas` evidence over the source SMT-LIB row.
