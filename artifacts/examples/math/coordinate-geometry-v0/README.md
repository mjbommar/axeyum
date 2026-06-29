# Coordinate Geometry V0

This pack covers small exact-rational coordinate-geometry examples for the
`geometry` field-extension row. It uses fixed points in the plane and exact
arithmetic, not diagrams or floating-point tolerances.

The examples are the geometry shadow that will later map to Axeyum's LRA/NRA
routes:

- midpoint replay for a segment;
- collinearity by a zero determinant;
- squared-distance replay for two points.

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
squared-distance identity. It does not yet emit SMT-LIB or call Axeyum's LRA/NRA
routes for these examples.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/coordinate-geometry-v0
```
