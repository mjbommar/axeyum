# Checks

## `triangle-distance-table`

Expected result: `sat`.

The validator checks the squared distance table for the triangle `(0,0)`,
`(3,0)`, `(0,4)`.

## `translation-isometry-witness`

Expected result: `sat`.

The validator checks that translating the triangle by `(1,-2)` preserves every
pairwise squared distance.

## `congruent-triangle-distance-witness`

Expected result: `sat`.

The validator checks that the triangle `(0,0)`, `(3,0)`, `(0,4)` and the
triangle `(1,1)`, `(1,4)`, `(5,1)` have the same pairwise squared distance
table.

## `bad-rigid-distance-table-rejected`

Expected result: `unsat`.

For the segment from `(0,0)` to `(3,0)`, exact replay gives:

```text
(3 - 0)^2 + (0 - 0)^2 = 9
```

The malformed row claims the same squared distance is `10`. The source SMT-LIB
artifact isolates the final exact-linear conflict:

```text
distance_squared = 9
distance_squared = 10
```

The QF_LRA route must emit checked `UnsatFarkas` evidence.

## `general-rigidity-geometry-lean-horizon`

Expected result: `not-run`.

This row records the proof-assistant target: graph rigidity, rigid-motion
classification, and synthetic rigidity theorems are not finite distance-table
replay.
