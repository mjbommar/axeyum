# Finite SDP Checks

This pack turns one two-by-two semidefinite-programming calculation into exact
rational resource rows. It checks only the listed matrix witness, trace
constraint, objective value, dual slack matrix, and zero duality gap; general
SDP strong duality and convex-optimization theorems remain proof horizons.

## Audience

- Learners connecting linear algebra, convex optimization, and exact replay.
- Resource authors who need a small SDP-style primal/dual witness with explicit
  trust boundaries.
- Solver developers looking for exact-rational QF_LRA/Farkas rows after replay.

## Checks

- `finite-sdp-primal-psd-replay`: checks the listed symmetric primal matrix is
  positive semidefinite by two-by-two principal minors.
- `finite-sdp-objective-replay`: recomputes the trace constraint and objective
  value from exact matrix entries.
- `finite-sdp-dual-slack-replay`: recomputes the dual slack matrix, checks it
  is positive semidefinite, and verifies the zero primal-dual gap.
- `bad-sdp-objective-rejected`: rejects the malformed claim that the same
  primal matrix has objective `0`; exact replay computes objective `1`.
- `general-sdp-duality-lean-horizon`: names the future proof route for general
  SDP duality, constraint qualifications, and strong-duality theorems.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-sdp-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_sdp_bad_objective_artifact_emits_checked_farkas
```

## Trust Boundary

Untrusted search may propose a primal matrix, dual variable, or slack matrix.
The trusted work is small: exact matrix arithmetic, two-by-two PSD principal
minor replay, objective replay, dual-gap arithmetic, and checked `UnsatFarkas`
evidence over the source SMT-LIB row.
