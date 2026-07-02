# Finite Root-Finding Checks

This pack turns root-finding algorithms into exact finite resource rows. It
checks only listed bisection and Newton steps over rational data; existence,
uniqueness, convergence rates, floating-point stability, and global behavior
remain proof or numerical-honesty horizons.

## Audience

- Learners connecting real algebra and calculus to numerical methods.
- Resource authors who need a finite algorithm trace with a checked bad row.
- Solver developers looking for exact-rational arithmetic rows that reduce to
  small QF_LRA/Farkas evidence after replay.

## Checks

- `bisection-bracket-replay`: checks one bisection step for `x^2 - 2` on
  `[1, 2]`.
- `newton-step-replay`: checks one Newton step from `x = 3/2`.
- `residual-decrease-witness`: checks that this fixed Newton step decreases
  the absolute residual.
- `bad-newton-step-rejected`: rejects the malformed claim that the next Newton
  iterate is `4/3` when exact replay computes `17/12`.
- `qf-lra-bad-newton-step`: checks the isolated exact-linear contradiction for
  the bad Newton iterate.
- `bad-bisection-width-rejected`: rejects the malformed claim that the selected
  bisection interval has width `1/3` when exact replay computes `1/2`.
- `qf-lra-bad-bisection-width`: checks the isolated exact-linear contradiction
  for the bad width excess.
- `general-root-finding-convergence-lean-horizon`: names the future proof
  route for convergence and existence theorems.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-root-finding-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_root_finding_bad_
```

## Trust Boundary

Untrusted search may propose an interval, iterate, or certificate. The trusted
work is small: exact polynomial evaluation, exact Newton/bisection arithmetic,
replay-only rejection of malformed source claims, and checked `UnsatFarkas`
evidence over separate source SMT-LIB proof rows.
