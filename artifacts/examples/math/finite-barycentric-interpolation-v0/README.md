# Finite Barycentric Interpolation Checks

This pack records exact rational barycentric interpolation replays for fixed
polynomials and node sets. It is a numerical-analysis and polynomial resource:
finite weights and interpolation values are replayed exactly, while general
interpolation uniqueness, error estimates, conditioning, spline theory, Runge
phenomena, and floating-point implementation claims stay in theorem or
numerical-honesty lanes.

## Validate

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-barycentric-interpolation-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_barycentric_interpolation_bad_value_artifact_emits_checked_farkas
```

## Checks

- `linear-barycentric-evaluation-witness` replays weights and evaluation for
  `1+2x` at nodes `0,2`.
- `quadratic-barycentric-evaluation-witness` replays weights and evaluation for
  `x^2` at nodes `0,1,3`.
- `node-hit-barycentric-witness` checks the removable-singularity case where
  the evaluation point is one of the nodes.
- `bad-barycentric-value-rejected` rejects a malformed finite interpolation
  value by exact replay.
- `qf-lra-bad-barycentric-value` routes the scalar contradiction through checked
  QF_LRA/Farkas evidence.
- `general-barycentric-interpolation-theory-lean-horizon` marks the missing
  theorem and numerical-honesty routes.

## Trust Boundary

```text
untrusted fast search -> barycentric weights, interpolation value, or Farkas certificate
trusted small checking -> exact rational replay plus checked QF_LRA/Farkas evidence
```
