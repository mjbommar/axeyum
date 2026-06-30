# Finite KKT Checks

This pack turns one constrained quadratic optimization calculation into exact
rational resource rows. It checks only the listed one-dimensional witness,
sample grid, stationarity equation, and complementary-slackness arithmetic;
general KKT necessity/sufficiency, constraint qualifications, SDP duality, and
algorithmic convergence remain proof horizons.

## Audience

- Learners connecting convexity, calculus, and linear algebra.
- Resource authors who need a small KKT witness with explicit trust boundaries.
- Solver developers looking for exact-rational QF_LRA/Farkas rows after replay.

## Checks

- `finite-quadratic-grid-minimum-replay`: checks the listed objective values on
  a finite feasible grid for `f(x) = (x - 2)^2` with `x <= 1`.
- `kkt-stationarity-replay`: checks the candidate `x = 1`, gradient `-2`,
  multiplier `2`, and stationarity residual `0`.
- `complementary-slackness-replay`: checks primal feasibility, dual
  feasibility, and complementary slackness for the same active constraint.
- `bad-kkt-stationarity-rejected`: rejects the malformed claim that multiplier
  `1` satisfies stationarity at the same point; exact replay computes residual
  `-1`, so the stationarity error from the claimed zero residual is `1`.
- `general-kkt-sufficiency-lean-horizon`: names the future proof route for
  general KKT theorems and convex optimization sufficiency.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-kkt-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_kkt_bad_stationarity_artifact_emits_checked_farkas
```

## Trust Boundary

Untrusted search may propose a feasible point, multiplier, or KKT certificate.
The trusted work is small: exact polynomial evaluation, exact derivative replay,
linear stationarity arithmetic, complementary-slackness multiplication, and
checked `UnsatFarkas` evidence over the source SMT-LIB row.
