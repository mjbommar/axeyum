# Checks

## `midpoint-witness`

Expected result: `sat`.

The validator recomputes the midpoint of `(0, 0)` and `(4, 2)` and checks it is
exactly `(2, 1)`.

## `collinearity-witness`

Expected result: `sat`.

The validator recomputes the two-dimensional determinant for `(0, 0)`, `(2, 2)`,
and `(5, 5)` and checks it is exactly zero.

## `distance-squared-witness`

Expected result: `sat`.

The validator recomputes the squared distance between `(1, 1)` and `(4, 5)` and
checks it is exactly `25`.
