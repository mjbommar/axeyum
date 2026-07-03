# Finite Cubic Hermite Interpolation Checks

This pack records exact rational cubic Hermite interpolation replays for fixed
polynomial rows. It is a calculus and numerical-analysis resource: endpoint
values, endpoint slopes, normalized parameters, Hermite basis values, scaled
derivative terms, and final values are replayed exactly, while Hermite
interpolation uniqueness, error bounds, spline theory, shape preservation, and
floating-point implementation claims stay in theorem or numerical-honesty lanes.

## Validate

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cubic-hermite-interpolation-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cubic_hermite_interpolation_bad_value_artifact_emits_checked_farkas
```

## Checks

- `smoothstep-hermite-witness` replays the cubic smoothstep row with zero
  endpoint slopes.
- `quadratic-unit-interval-hermite-witness` replays endpoint value/slope data
  for `1+x+x^2` on `[0,1]`.
- `quadratic-nonunit-interval-hermite-witness` replays endpoint value/slope
  data for `x^2` on `[1,3]`, including interval-length scaling.
- `bad-hermite-value-rejected` rejects a malformed Hermite value by exact
  replay.
- `qf-lra-bad-hermite-value` routes the scalar contradiction through checked
  QF_LRA/Farkas evidence.
- `general-hermite-interpolation-theory-lean-horizon` marks the missing theorem
  and numerical-honesty routes.

## Trust Boundary

```text
untrusted fast search -> Hermite coefficients, endpoint slopes, value, or Farkas certificate
trusted small checking -> exact rational Hermite replay plus checked QF_LRA/Farkas evidence
```
