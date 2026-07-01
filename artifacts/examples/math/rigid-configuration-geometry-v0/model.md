# Model

Points are two-element arrays of exact rational strings:

```json
["3", "0"]
```

A finite rigid configuration stores pairwise squared distances. For a triangle:

```json
{"ab": "9", "ac": "16", "bc": "25"}
```

Squared distance is replayed exactly:

```text
(x2 - x1)^2 + (y2 - y1)^2
```

## Triangle Distance Table

The triangle `(0,0)`, `(3,0)`, `(0,4)` has:

```text
AB^2 = 9
AC^2 = 16
BC^2 = 25
```

The validator also checks that the triangle is nondegenerate.

## Translation Isometry

Translation by `(1,-2)` sends:

```text
(0,0) -> (1,-2)
(3,0) -> (4,-2)
(0,4) -> (1,2)
```

The target triangle has the same squared distance table.

## Bad Translation Image

The promoted bad translation row uses source point `(3,0)` and translation
`(1,-2)`. Exact replay computes:

```text
(3,0) + (1,-2) = (4,-2)
```

The malformed row claims the translated x-coordinate is `5`. The QF_LRA
artifact checks only the final conflict:

```text
target_b_x = 4
target_b_x = 5
```

## Congruent Triangles

The triangles:

```text
(0,0), (3,0), (0,4)
(1,1), (1,4), (5,1)
```

share squared side lengths `9`, `16`, and `25`.

## Bad Distance Table

The promoted bad row uses the segment `(0,0)` to `(3,0)`. Exact replay
computes:

```text
(3 - 0)^2 + (0 - 0)^2 = 9
```

The malformed row claims the squared distance is `10`. The QF_LRA artifact
checks only the final conflict:

```text
distance_squared = 9
distance_squared = 10
```

These fixed distance-table checks are finite exact-rational replay targets.
They are not general graph-rigidity or synthetic Euclidean geometry theorems.
