# Checks

## `affine-map-point-witness`

Expected result: `sat`.

The validator recomputes `A*p + b` for the fixed point `(2, 1)` and checks that
the exact image is `(6, 4)`.

## `affine-midpoint-preservation`

Expected result: `sat`.

The validator recomputes the midpoint of `(0, 0)` and `(4, 2)`, applies the
affine map to the endpoints and midpoint, and checks that the image of the
midpoint equals the midpoint of the images.

## `bad-midpoint-image-y-rejected`

Expected result: `unsat`.

The validator recomputes the segment midpoint and affine midpoint image:
`T(2, 1) = (6, 4)`. The malformed row claims image y-coordinate `5`. The final
coordinate conflict is also checked by a linked `QF_LRA` artifact and a
resource-backed `UnsatFarkas` regression.

## `affine-collinearity-preservation`

Expected result: `sat`.

The validator checks the matrix determinant, recomputes the three listed
images, and verifies that both the source triple and image triple have zero
two-dimensional collinearity determinant.

## `bad-distance-preservation-rejected`

Expected result: `unsat`.

The validator rejects the false claim that the affine map preserves Euclidean
squared distance for the listed segment: the original squared distance is `1`
and the transformed squared distance is `5`. The final equality conflict is
also checked by a linked `QF_LRA` artifact and a resource-backed
`UnsatFarkas` regression.

## `general-affine-geometry-lean-horizon`

Expected result: `not-run`.

General affine-combination, incidence, ratio, and synthetic-geometry theorems
belong in a future Lean-backed resource. The finite rows above are exact
replay checks only.
