# Orientation And Area Geometry V0

This pack extends the `geometry` field with exact-rational orientation and
signed-area checks in the plane. It follows `coordinate-geometry-v0` and
`affine-geometry-v0`: coordinate witnesses now carry the orientation/area data
needed for triangle predicates, affine area scaling, and barycentric replay.

The pack covers:

- counterclockwise orientation and signed double-area replay for one triangle;
- affine area scaling by the determinant of a fixed invertible affine map;
- barycentric point replay for a point inside a fixed triangle;
- checked QF_LRA/Farkas rejection of a false affine-area-preservation claim
  and a false orientation claim;
- a Lean-horizon row for general orientation and area theorems.

## Concepts

- `field_geometry`
- `field_linear_algebra`
- `field_real_analysis`
- `curriculum_reals`
- `curriculum_linear_algebra`
- `curriculum_polynomials`

## Trust Story

The validator parses all coordinates, matrix entries, determinants, weights,
and areas as exact rational strings. It recomputes signed double areas with the
two-dimensional determinant, applies affine maps exactly, and checks
barycentric coordinates without floating point. The false affine-area
preservation and false orientation rows are also routed through Axeyum's
checked `UnsatFarkas` evidence path.

This is still a finite replay pack. It does not claim general theorems about
all oriented manifolds, all Euclidean geometries, or all affine spaces.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/orientation-area-geometry-v0
```
