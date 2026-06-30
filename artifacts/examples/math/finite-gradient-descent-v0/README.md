# Finite Gradient Descent Checks

This pack turns one exact rational gradient-descent step for a two-variable
quadratic into resource rows. It checks only the listed gradient, step update,
objective decrease, and finite descent-bound arithmetic; global convergence
rates and optimization-algorithm theorems remain proof horizons.

## Audience

- Learners connecting calculus, linear algebra, and numerical optimization.
- Resource authors who need a small exact descent-step witness with explicit
  trust boundaries.
- Solver developers looking for exact-rational QF_LRA/Farkas rows after replay.

## Checks

- `quadratic-gradient-replay`: recomputes the gradient and Hessian of the fixed
  quadratic at the listed start point.
- `gradient-descent-step-replay`: checks `x_next = x_start - alpha * grad`.
- `descent-bound-replay`: recomputes the objective values, exact decrease,
  gradient-norm square, finite descent lower bound, and positive slack.
- `bad-descent-value-rejected`: rejects the malformed claim that the same step
  decreases the objective by only `2`; exact replay computes decrease `11/4`.
- `general-gradient-descent-convergence-lean-horizon`: names the future proof
  route for convergence rates, smooth convex descent lemmas, and stopping
  criteria.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-gradient-descent-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_gradient_descent_bad_decrease_artifact_emits_checked_farkas
```

## Trust Boundary

Untrusted search may propose a step size, gradient, next point, or descent
certificate. The trusted work is small: exact matrix-vector multiplication,
exact rational objective replay, exact step arithmetic, descent-bound replay,
and checked `UnsatFarkas` evidence over the source SMT-LIB row.
