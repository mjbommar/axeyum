# Checks

## `midpoint-witness`

Expected result: `sat`.

The validator recomputes the midpoint of `(0, 0)` and `(4, 2)` and checks it is
exactly `(2, 1)`.

## `bad-midpoint-x-rejected`

Expected result: `unsat`.

For the segment from `(0,0)` to `(4,2)`, exact replay computes midpoint
`(2,1)`. The malformed row claims the midpoint x-coordinate is `3`; the source
SMT-LIB artifact isolates that final exact-linear conflict and the QF_LRA route
checks Farkas evidence.

## `collinearity-witness`

Expected result: `sat`.

The validator recomputes the two-dimensional determinant for `(0, 0)`, `(2, 2)`,
and `(5, 5)` and checks it is exactly zero.

## `distance-squared-witness`

Expected result: `sat`.

The validator recomputes the squared distance between `(1, 1)` and `(4, 5)` and
checks it is exactly `25`.

## `bad-distance-squared-rejected`

Expected result: `unsat`.

The fixed points are still `(1, 1)` and `(4, 5)`, so exact replay computes
squared distance `25`. The malformed row claims the same squared distance is
`26`; the source SMT-LIB artifact isolates that final exact-linear conflict and
the QF_LRA route checks Farkas evidence.
