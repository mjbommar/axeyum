# Finite Active-Set Quadratic Program Checks

This pack turns one exact rational active-set quadratic-program trace into
resource rows. It checks only the listed two-variable quadratic, active face,
inactive constraint, KKT multipliers, and a false active-set candidate; general
active-set convergence and finite-termination theorems remain proof horizons.

## Audience

- Learners connecting constrained optimization, active sets, and KKT replay.
- Resource authors who need a small active-set example with explicit trust
  boundaries.
- Solver developers looking for exact-rational QF_LRA/Farkas rows after replay.

## Checks

- `unconstrained-minimizer-replay`: recomputes the unconstrained minimizer,
  zero gradient, objective value, and violation of the active upper bound.
- `active-face-candidate-replay`: checks the active face `x = 1`, the free
  coordinate solve `y = 1`, and the resulting candidate objective.
- `active-set-kkt-replay`: checks constraint values, nonnegative multipliers,
  stationarity, and complementary slackness.
- `inactive-constraint-slack-replay`: checks the inactive lower-bound slack and
  zero inactive multiplier.
- `bad-active-set-free-gradient-rejected`: rejects the malformed claim that the
  feasible candidate `(1,0)` solves the same active-face subproblem.
- `general-active-set-method-lean-horizon`: names the future proof route for
  active-set finite termination, degeneracy handling, and convergence theorems.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-active-set-qp-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_active_set_qp_bad_free_gradient_artifact_emits_checked_farkas
```

## Trust Boundary

Untrusted search may propose an active set, candidate point, or multiplier
table. The trusted work is small: exact objective/gradient replay, exact
constraint evaluation, exact stationarity and complementarity arithmetic, and
checked `UnsatFarkas` evidence over the source SMT-LIB row.
