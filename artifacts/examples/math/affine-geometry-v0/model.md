# Model

Points are two-element arrays of exact rational strings:

```json
["2", "1/3"]
```

An affine map is represented by a two-by-two matrix and a two-dimensional
translation vector:

```json
{
  "matrix": [["2", "1"], ["1", "3"]],
  "translation": ["1", "-1"]
}
```

The image of a point is:

```text
T(x, y) = (2x + y + 1, x + 3y - 1)
```

## Checks

### Point Image

For `p = (2, 1)`:

```text
T(p) = (2*2 + 1 + 1, 2 + 3*1 - 1) = (6, 4)
```

### Midpoint Preservation

For `A = (0, 0)` and `B = (4, 2)`, the midpoint is `M = (2, 1)`.
The map sends:

```text
T(A) = (1, -1)
T(B) = (11, 9)
T(M) = (6, 4)
```

The midpoint of `T(A)` and `T(B)` is also `(6, 4)`.

### Collinearity Preservation

The points `(0, 0)`, `(1, 1)`, and `(3, 3)` are collinear. The matrix has
determinant `5`, so the finite witness uses an invertible affine map. Their
images `(1, -1)`, `(4, 3)`, and `(10, 11)` are collinear because the
two-dimensional determinant is exactly zero.

### False Distance Preservation

Affine maps do not generally preserve Euclidean distance. For `P = (0, 0)` and
`Q = (1, 0)`, the original squared distance is `1`. Their images are `(1, -1)`
and `(3, 0)`, whose squared distance is `5`.

These are exact finite replay targets, not a complete formalization of affine
geometry.
