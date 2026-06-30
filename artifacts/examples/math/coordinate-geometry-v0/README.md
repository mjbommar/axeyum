# Coordinate Geometry V0

This pack covers small exact-rational coordinate-geometry examples for the
`geometry` field-extension row. It uses fixed points in the plane and exact
arithmetic, not diagrams or floating-point tolerances.

The examples are the geometry shadow that will later map to Axeyum's LRA/NRA
routes:

- midpoint replay for a segment;
- collinearity by a zero determinant;
- squared-distance replay for two points;
- checked QF_LRA/Farkas rejection of a malformed squared-distance row.

## Concepts

- `field_geometry`
- `field_linear_algebra`
- `field_real_analysis`
- `curriculum_reals`
- `curriculum_linear_algebra`
- `curriculum_polynomials`

## Trust Story

The current validator parses point coordinates exactly as rational strings. It
checks midpoint equations, a two-dimensional collinearity determinant, and a
squared-distance identity. The promoted bad row keeps nonlinear distance
arithmetic in exact replay, then checks the final linear contradiction between
computed squared distance `25` and claimed squared distance `26` through the
QF_LRA/Farkas route.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/coordinate-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes coordinate_geometry_bad_distance_squared_artifact_emits_checked_farkas
```
