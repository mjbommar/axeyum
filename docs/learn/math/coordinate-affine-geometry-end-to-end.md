# End To End: Coordinate And Affine Geometry

This lesson follows exact finite geometry resources from coordinate midpoint,
collinearity, and distance replay to affine maps, signed area, barycentric
coordinates, and checked false geometry claims. It uses
[coordinate-geometry-v0](../../../artifacts/examples/math/coordinate-geometry-v0/),
[affine-geometry-v0](../../../artifacts/examples/math/affine-geometry-v0/),
and
[orientation-area-geometry-v0](../../../artifacts/examples/math/orientation-area-geometry-v0/).
For exact point-on-line and line-intersection replay, use
[incidence-geometry-v0](../../../artifacts/examples/math/incidence-geometry-v0/)
and [Incidence Geometry](incidence-geometry-end-to-end.md).
For the theorem boundary around finite incidence rows, use
[Incidence Geometry Theorem Boundary](incidence-geometry-theorem-boundary.md).
For exact distance-table and finite isometry replay, use
[rigid-configuration-geometry-v0](../../../artifacts/examples/math/rigid-configuration-geometry-v0/)
and
[Rigid Configuration Geometry](rigid-configuration-geometry-end-to-end.md).
For the boundary between finite affine-coordinate replay and general affine,
projective, and synthetic geometry, use
[Affine Geometry Theorem Boundary](affine-geometry-theorem-boundary.md).
For exact circle point, tangent-line, and chord-midpoint replay, use
[finite-circle-geometry-v0](../../../artifacts/examples/math/finite-circle-geometry-v0/)
and [Finite Circle Geometry](finite-circle-geometry-end-to-end.md).
For exact unit-circle inversion replay, use
[finite-inversion-geometry-v0](../../../artifacts/examples/math/finite-inversion-geometry-v0/)
and [Finite Inversion Geometry](finite-inversion-geometry-end-to-end.md).
For exact cyclic quadrilateral replay, use
[finite-cyclic-geometry-v0](../../../artifacts/examples/math/finite-cyclic-geometry-v0/)
and [Finite Cyclic Geometry](finite-cyclic-geometry-end-to-end.md).

Concept rows:

- `curriculum_reals`, `curriculum_linear_algebra`, and
  `curriculum_polynomials` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_geometry`, `field_linear_algebra`, and `field_real_analysis` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)
- `bridge_coordinate_orientation_geometry` and
  `bridge_finite_circle_inversion_cyclic_replay` in the Foundational Concept
  Atlas.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `midpoint-witness` | `sat` | replay-only |
| `collinearity-witness` | `sat` | replay-only |
| `distance-squared-witness` | `sat` | replay-only |
| `bad-distance-squared-rejected` | `unsat` | checked QF_LRA/Farkas |
| `affine-map-point-witness` | `sat` | replay-only |
| `affine-midpoint-preservation` | `sat` | replay-only |
| `bad-midpoint-image-y-rejected` | `unsat` | checked QF_LRA/Farkas |
| `affine-collinearity-preservation` | `sat` | replay-only |
| `bad-collinearity-determinant-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-distance-preservation-rejected` | `unsat` | checked QF_LRA/Farkas |
| `triangle-orientation-witness` | `sat` | replay-only |
| `affine-area-scaling` | `sat` | replay-only |
| `bad-affine-area-scaling-rejected` | `unsat` | checked |
| `barycentric-point-inside` | `sat` | replay-only |
| `bad-orientation-rejected` | `unsat` | checked |
| `point-on-circle-witness` | `sat` | replay-only |
| `tangent-line-witness` | `sat` | replay-only |
| `chord-midpoint-perpendicular-witness` | `sat` | replay-only |
| `circle-line-intersection-witness` | `sat` | replay-only |
| `bad-circle-radius-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-circle-line-intersection-rejected` | `unsat` | checked QF_LRA/Farkas |
| `inversion-image-witness` | `sat` | replay-only |
| `inverse-distance-product-witness` | `sat` | replay-only |
| `inversion-collinearity-witness` | `sat` | replay-only |
| `bad-inversion-image-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-inverse-distance-product-rejected` | `unsat` | checked QF_LRA/Farkas |
| `cyclic-quadrilateral-witness` | `sat` | replay-only |
| `cyclic-diagonal-intersection-witness` | `sat` | replay-only |
| `cyclic-opposite-right-angles-witness` | `sat` | replay-only |
| `cyclic-ptolemy-rectangle-witness` | `sat` | replay-only |
| `bad-cyclic-diagonal-intersection-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-cyclic-opposite-angle-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-cyclic-ptolemy-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-affine-geometry-lean-horizon` | `not-run` | lean-horizon |
| `general-oriented-geometry-lean-horizon` | `not-run` | lean-horizon |
| `general-circle-geometry-lean-horizon` | `not-run` | lean-horizon |
| `general-inversion-geometry-lean-horizon` | `not-run` | lean-horizon |
| `general-cyclic-geometry-lean-horizon` | `not-run` | lean-horizon |

Every row uses exact rational coordinates. The packs do not claim general
Euclidean, affine, oriented-geometry, circle-geometry, inversion-geometry, or
cyclic-geometry theorems.

The shared `bridge_finite_circle_inversion_cyclic_replay` row is the atlas
vocabulary for these finite circle, inversion, and cyclic packs. It exists so
consumers can find the checked finite coordinate/Farkas route without reading
that bridge as a proof of general circle, inversion, angle, Ptolemy, or
synthetic geometry theorems.

## Replay Coordinate Facts

The midpoint row uses:

```text
A = (0, 0)
B = (4, 2)
M = (2, 1)
```

The validator recomputes:

```text
((0 + 4) / 2, (0 + 2) / 2) = (2, 1)
```

The collinearity row uses `(0,0)`, `(2,2)`, and `(5,5)`. The validator
recomputes the two-dimensional determinant:

```text
det((2,2), (5,5)) = 2*5 - 2*5 = 0
```

The distance row checks:

```text
(1,1) to (4,5)
distance^2 = (4 - 1)^2 + (5 - 1)^2 = 3^2 + 4^2 = 25
```

These are finite coordinate calculations, not diagram reasoning.

## Reject Bad Coordinate Claims

The midpoint bad row keeps the same segment:

```text
A = (0,0)
B = (4,2)
```

Exact replay computes midpoint `(2,1)`. The malformed row claims the midpoint
x-coordinate is `3`, so the source QF_LRA artifact checks only:

```text
midpoint_x = 2
midpoint_x = 3
```

The coordinate-geometry bad row keeps the same fixed points:

```text
P = (1,1)
Q = (4,5)
```

Exact replay computes:

```text
distance^2(P,Q) = 25
```

The malformed row claims `distance^2(P,Q) = 26`. The source QF_LRA artifact
checks only the final exact-linear contradiction:

```text
distance_squared = 25
distance_squared = 26
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

## Replay An Affine Map

The affine map is:

```text
A = [[2, 1],
     [1, 3]]
b = [1, -1]
T(p) = A*p + b
```

For `p = (2,1)`, the validator checks:

```text
T(2,1) = (2*2 + 1*1 + 1, 1*2 + 3*1 - 1) = (6,4)
```

For the segment from `(0,0)` to `(4,2)`, it also checks midpoint
preservation:

```text
T(0,0) = (1,-1)
T(4,2) = (11,9)
T(2,1) = (6,4)
midpoint((1,-1), (11,9)) = (6,4)
```

## Reject A Bad Affine Midpoint Coordinate

The bad midpoint row keeps the same segment and affine map. Exact replay
computes:

```text
M = midpoint((0,0), (4,2)) = (2,1)
T(M) = (6,4)
```

The malformed row claims the midpoint image has y-coordinate `5`. The source
QF_LRA artifact checks only the final exact-linear contradiction:

```text
image_midpoint_y = 4
image_midpoint_y = 5
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

For the collinear triple `(0,0)`, `(1,1)`, `(3,3)`, the same map has
determinant `5` and sends the points to:

```text
(1,-1), (4,3), (10,11)
```

The validator recomputes the image determinant and checks collinearity.

The bad collinearity row keeps the same image triple. Exact replay computes
image determinant `0`, while the source QF_LRA artifact checks the malformed
claim that the image determinant is `1`.

## Reject False Distance Preservation

The affine map above is not an isometry. The bad row uses:

```text
p = (0,0)
q = (1,0)
T(p) = (1,-1)
T(q) = (3,0)
```

The trusted checker recomputes:

```text
distance^2(p,q) = 1
distance^2(T(p),T(q)) = 5
```

The affine pack exposes the rejected preservation claim as a `QF_LRA`
contradiction:

```text
original_distance_squared = 1
transformed_distance_squared = 5
original_distance_squared = transformed_distance_squared
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

So the claim that this arbitrary affine map preserves Euclidean squared
distance is checked `unsat`.

## Replay Orientation And Area

The oriented triangle is:

```text
(0,0), (4,0), (1,3)
```

The validator recomputes the signed double area:

```text
det((4,0), (1,3)) = 12
area = 6
orientation = counterclockwise
```

Under the same affine map, the image triangle is:

```text
(1,-1), (9,3), (6,9)
```

The determinant of the linear part is `5`, so the validator checks:

```text
image signed double area = 60 = 5 * 12
```

## Reject A Bad Area Scaling Claim

The bad row keeps the exact affine replay above, then claims the image signed
double area is unchanged:

```text
source_signed_double_area = 12
image_signed_double_area = 60
image_signed_double_area = source_signed_double_area
```

The resource regression checks this final equality conflict as `QF_LRA`, and
the `unsat` result must carry `Evidence::UnsatFarkas`.

## Replay Barycentric Coordinates

For the same source triangle, the barycentric weights are:

```text
1/4, 1/2, 1/4
```

The validator checks:

```text
1/4 + 1/2 + 1/4 = 1
1/4*(0,0) + 1/2*(4,0) + 1/4*(1,3) = (9/4, 3/4)
```

All weights are nonnegative, so this is a finite point-inside witness for the
fixed triangle.

## Reject A Bad Orientation

The bad row claims this triangle is counterclockwise:

```text
(0,0), (0,1), (1,0)
```

The validator recomputes:

```text
signed double area = -1
orientation = clockwise
```

The resource regression checks the final orientation contradiction as
`QF_LRA`:

```text
signed_double_area = -1
signed_double_area > 0
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

The false orientation claim is checked `unsat`.

## Name The Lean Horizon

The packs do not claim broad geometry theory:

```text
all affine-space theorems
all Euclidean geometry theorems
synthetic geometry translations
oriented manifolds
general barycentric-coordinate theorems
diagrammatic incidence reasoning
power-of-a-point, inversion, and cyclic quadrilateral theorems
angle preservation and circle-line inversion correspondences
Ptolemy and general angle-chasing theorems
```

Those require Lean-backed geometry resources or explicitly scoped algebraic
proof certificates. These packs only check finite exact-rational coordinate,
affine, determinant, barycentric, circle, inversion, and cyclic obligations.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/coordinate-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes coordinate_geometry_bad_midpoint_x_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes coordinate_geometry_bad_distance_squared_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/affine-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes affine_geometry_bad_midpoint_image_y_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/orientation-area-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes orientation_area_bad_affine_area_scaling_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-circle-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_circle_geometry_bad_radius_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-inversion-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_inversion_geometry_bad_inverse_x_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_inversion_geometry_bad_inverse_distance_product_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cyclic-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cyclic_geometry_bad_diagonal_intersection_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cyclic_geometry_bad_opposite_angle_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cyclic_geometry_bad_ptolemy_artifact_emits_checked_farkas
```

Expected output for each command:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite geometry resource pattern:

```text
untrusted fast search -> point, map, area, circle, inversion, cyclic, barycentric, or counterexample row
trusted small checking -> exact rational coordinate, determinant, scale, midpoint, and dot-product replay
proof upgrade -> QF_LRA/Farkas certificates for false distance/orientation/radius/inverse/intersection rows
remaining horizon -> general affine, Euclidean, oriented, circle, inversion, and cyclic geometry proofs
```

The graduation route is deterministic exact-rational replay plus checked proof
objects for false geometry claims before broader synthetic or analytic geometry
claims are promoted.
