# Checks

## `triangle-orientation-witness`

Expected result: `sat`.

The validator recomputes the signed double area of the triangle
`(0, 0), (4, 0), (1, 3)` and checks that it is `12`, so the listed orientation
is counterclockwise and the ordinary area is `6`.

## `affine-area-scaling`

Expected result: `sat`.

The validator checks that the affine map has determinant `5`, recomputes the
three image points, and verifies that the image triangle's signed double area
is `60`, exactly `5 * 12`.

## `barycentric-point-inside`

Expected result: `sat`.

The validator checks that the weights `1/4, 1/2, 1/4` sum to `1`, are
nonnegative, and replay the point `(9/4, 3/4)` as a barycentric combination of
the triangle vertices.

## `bad-orientation-rejected`

Expected result: `unsat`.

The validator rejects the false claim that the clockwise triangle
`(0, 0), (0, 1), (1, 0)` is counterclockwise: its signed double area is `-1`.

## `general-oriented-geometry-lean-horizon`

Expected result: `not-run`.

General orientation, area, and affine-volume theorems belong in a future
Lean-backed resource. The finite rows above are exact replay checks only.
