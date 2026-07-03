# Finite Divided Difference Checks

This pack records exact rational Newton divided-difference replays for fixed
polynomials and node sets. It is a numerical-analysis and polynomial resource:
finite tables are replayed exactly, while general interpolation uniqueness,
error estimates, conditioning, spline theory, and floating-point
implementation claims stay in theorem or numerical-honesty lanes.

## Validate

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-divided-differences-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_divided_differences_bad_interpolation_value_artifact_emits_checked_farkas
```

## Checks

- `quadratic-divided-difference-table` replays the divided-difference table for
  `1+x^2` at nodes `0,1,2`.
- `quadratic-newton-evaluation-witness` evaluates that Newton form at `x=3`.
- `cubic-divided-difference-table` repeats the finite replay for `x^3`.
- `bad-interpolation-value-rejected` rejects a malformed finite interpolation
  value by exact replay.
- `qf-lra-bad-interpolation-value` routes the scalar contradiction through
  checked QF_LRA/Farkas evidence.
- `general-interpolation-theory-lean-horizon` marks the missing theorem route.

## Trust Boundary

```text
untrusted fast search -> divided-difference table, interpolation value, or Farkas certificate
trusted small checking -> exact rational replay plus checked QF_LRA/Farkas evidence
```
