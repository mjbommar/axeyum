# Finite Hyperplane Separation Checks

This pack turns a convex-hull separation argument into exact rational resource
rows. It checks only listed finite points, weights, and separator scores; general
separation theorems, Hahn-Banach-style arguments, SDP duality, and algorithmic
convergence remain proof horizons.

## Audience

- Learners connecting convexity, linear algebra, and real analysis.
- Resource authors who need a finite convex-hull/separator example.
- Solver developers looking for exact-rational QF_LRA/Farkas rows after replay.

## Checks

- `convex-combination-replay`: checks that `(1/3, 1/3)` is a convex
  combination of the triangle vertices `(0,0)`, `(1,0)`, and `(0,1)`.
- `bad-convex-combination-point-rejected`: rejects the malformed claim that
  the same convex weights produce x-coordinate `1/2` by exact replay.
- `qf-lra-bad-convex-combination-point`: checks the fixed Farkas contradiction
  exposed by that replay row.
- `separating-hyperplane-replay`: checks that `x + y <= 1` separates that
  triangle from the outside point `(2,2)`.
- `supporting-face-replay`: checks that the tight face is represented by the
  vertices `(1,0)` and `(0,1)`.
- `bad-separator-rejected`: rejects the malformed claim that the outside score
  also satisfies the triangle bound by exact replay.
- `qf-lra-bad-separator`: checks the fixed Farkas contradiction exposed by the
  separator replay row.
- `general-separation-theorem-lean-horizon`: names the future proof route for
  general hyperplane separation and duality theorems.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-separation-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_separation_bad_
```

## Trust Boundary

Untrusted search may propose vertices, weights, a separating normal, or a
certificate. The trusted work is small: exact convex-combination replay, exact
dot-product replay, tight-face checking, and checked `UnsatFarkas` evidence over
the separate source-linked `qf-lra-*` rows.
