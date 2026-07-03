# Finite Cubic Spline Interpolation Checks

This pack records one exact rational natural cubic spline assembly over the
knots `0, 1, 2` with values `0, 1, 0`. It checks the two cubic pieces, endpoint
sample values, interior `C1` and `C2` continuity, natural endpoint
second-derivative constraints, and midpoint values.

The pack is intentionally finite. It does not claim general spline existence,
uniqueness, error estimates, shape preservation, convergence, or floating-point
spline implementation correctness.

## Validation

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cubic-spline-interpolation-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cubic_spline_interpolation_bad_value_artifact_emits_checked_farkas
```

## Checks

- `natural-spline-left-midpoint-witness` replays the left interval midpoint
  value `11/16`.
- `natural-spline-right-midpoint-witness` replays the symmetric right interval
  midpoint value `11/16`.
- `natural-spline-knot-smoothness-witness` replays value, first-derivative, and
  second-derivative matching at the interior knot.
- `bad-spline-value-rejected` rejects a malformed midpoint value by exact
  replay.
- `qf-lra-bad-spline-value` routes the scalar contradiction through checked
  QF_LRA/Farkas evidence.
- `general-spline-interpolation-theory-lean-horizon` marks the theorem and
  numerical-analysis boundary.

## Trust Boundary

```text
untrusted fast search -> spline pieces, midpoint value, or Farkas certificate
trusted small checking -> exact rational spline replay plus checked QF_LRA/Farkas evidence
```
