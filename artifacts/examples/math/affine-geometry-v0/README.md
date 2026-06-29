# Affine Geometry V0

This pack deepens the `geometry` field with exact-rational affine geometry in
the plane. It is the next step after `coordinate-geometry-v0`: instead of only
checking individual points and distances, it checks a fixed affine map

```text
T(p) = A p + b
```

and replays the finite facts that affine maps preserve affine combinations and
incidence.

The pack covers:

- exact point-image replay for one affine map;
- midpoint preservation for a fixed segment;
- collinearity preservation for a fixed triple;
- checked rejection of the false claim that arbitrary affine maps preserve
  Euclidean distance;
- a Lean-horizon row for general affine-geometry theorems.

## Concepts

- `field_geometry`
- `field_linear_algebra`
- `field_real_analysis`
- `curriculum_reals`
- `curriculum_linear_algebra`
- `curriculum_polynomials`

## Trust Story

The current validator parses all coordinates, matrix entries, and translations
as exact rational strings. It recomputes every affine image and determinant
without floating point. The false distance-preservation row is checked by
explicit counterexample replay: the original squared distance is `1`, while the
transformed squared distance is `5`.

This is still a finite replay pack. It does not claim a general theorem about
all affine maps or all geometries.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/affine-geometry-v0
```
