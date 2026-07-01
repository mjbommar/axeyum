# Finite Proximal Gradient Checks

This pack turns exact rational proximal-gradient steps for an L1-regularized
quadratic into resource rows. It checks the listed smooth gradient, trial
step, soft-threshold proximal operator, box-plus-L1 constrained proximal
operator, composite objective decrease, false proximal-optimality obstruction,
and false box-feasibility obstruction; general proximal-gradient convergence
and composite-optimization theorems remain proof horizons.

## Audience

- Learners connecting calculus, convex optimization, and nonsmooth penalties.
- Resource authors who need a small proximal-step witness with explicit trust
  boundaries.
- Solver developers looking for exact-rational QF_LRA/Farkas rows after replay.

## Checks

- `proximal-gradient-gradient-replay`: recomputes the derivative of the smooth
  quadratic at the starting point.
- `proximal-trial-step-replay`: checks the ordinary gradient trial point before
  the proximal map.
- `soft-threshold-prox-replay`: checks the L1 soft-threshold proximal value and
  positive-branch optimality residual.
- `composite-decrease-replay`: checks the smooth-plus-L1 composite objective
  value before and after the step.
- `box-plus-l1-prox-replay`: checks that the constrained proximal point over
  `[0,3/4]` clips the unconstrained point `1` to `3/4` with active upper
  multiplier `1/2`.
- `bad-proximal-point-rejected`: rejects a malformed proximal point with checked
  QF_LRA/Farkas evidence.
- `bad-box-proximal-point-rejected`: rejects a malformed box-plus-L1 proximal
  point that violates the upper bound with checked QF_LRA/Farkas evidence.
- `general-proximal-gradient-convergence-lean-horizon`: names the future proof
  route for convergence, rates, and nonsmooth convex analysis.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-proximal-gradient-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_proximal_gradient_bad_
```

## Trust Boundary

Untrusted search may propose a step size, trial point, proximal point, or
optimality certificate. The trusted work is small: exact derivative replay,
exact gradient-step arithmetic, exact soft-threshold replay, exact composite
objective evaluation, exact box projection with active multiplier replay, and
checked `UnsatFarkas` evidence over the source SMT-LIB rows.
