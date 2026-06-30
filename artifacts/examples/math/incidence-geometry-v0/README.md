# Incidence Geometry V0

This pack extends the `geometry` field with exact-rational line-incidence
checks in the plane. It keeps geometry in the same finite replay style as the
coordinate, affine, and orientation packs: line equations are committed as
small rational tables, and every claim is recomputed before any solver evidence
is trusted.

The pack covers:

- line-equation replay for two fixed points;
- intersection replay for two non-parallel lines;
- point-on-line replay;
- checked QF_LRA/Farkas rejection of a false incidence claim;
- a Lean-horizon row for projective and synthetic incidence theorems.

## Concepts

- `field_geometry`
- `field_linear_algebra`
- `field_real_analysis`
- `curriculum_reals`
- `curriculum_linear_algebra`
- `curriculum_polynomials`

## Trust Story

The validator parses all coordinates and line coefficients as exact rational
strings. It recomputes `a*x + b*y + c`, checks non-parallel intersection rows,
and rejects malformed point-on-line claims without floating point.

The promoted bad row keeps the nonlinear or diagrammatic parts out of the
solver. Exact replay computes a single line value, and the source SMT-LIB
artifact checks only the final linear contradiction through Axeyum's
`UnsatFarkas` evidence path.

This pack does not claim projective geometry, synthetic incidence theorems,
Pascal/Brianchon-style theorems, or diagrammatic reasoning.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/incidence-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes incidence_geometry_bad_point_on_line_artifact_emits_checked_farkas
```
