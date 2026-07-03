# Finite Difference Derivative Checks

This pack records exact rational finite-difference derivative replays for fixed
polynomials and stencil rows. It is a calculus and numerical-analysis resource:
finite stencil arithmetic is replayed exactly, while truncation error,
convergence order, stability, PDE discretization theory, and floating-point
implementation claims stay in theorem or numerical-honesty lanes.

## Validate

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-difference-derivatives-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_difference_derivatives_bad_value_artifact_emits_checked_farkas
```

## Checks

- `forward-difference-affine-exact-witness` replays a forward first-derivative
  stencil for `1+3x`.
- `central-difference-quadratic-exact-witness` replays a central
  first-derivative stencil for `1+2x+x^2`.
- `second-central-difference-quadratic-exact-witness` replays a central
  second-derivative stencil for the same quadratic.
- `bad-finite-difference-value-rejected` rejects a malformed finite derivative
  value by exact replay.
- `qf-lra-bad-finite-difference-value` routes the scalar contradiction through
  checked QF_LRA/Farkas evidence.
- `general-finite-difference-theory-lean-horizon` marks the missing theorem and
  numerical-honesty routes.

## Trust Boundary

```text
untrusted fast search -> stencil weights, derivative value, or Farkas certificate
trusted small checking -> exact rational stencil replay plus checked QF_LRA/Farkas evidence
```
