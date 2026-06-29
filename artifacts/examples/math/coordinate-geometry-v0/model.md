# Model

Points are two-element arrays of exact rational strings:

```json
["2", "1/3"]
```

No floating-point arithmetic is used.

## Checks

### Midpoint

For `A = (0, 0)` and `B = (4, 2)`, the midpoint is:

```text
M = ((0 + 4) / 2, (0 + 2) / 2) = (2, 1)
```

### Collinearity

For `A = (0, 0)`, `B = (2, 2)`, and `C = (5, 5)`, the determinant

```text
(Bx - Ax)(Cy - Ay) - (By - Ay)(Cx - Ax)
```

is exactly zero, so the three fixed points are collinear.

### Squared Distance

For `P = (1, 1)` and `Q = (4, 5)`, the squared distance is:

```text
(4 - 1)^2 + (5 - 1)^2 = 25
```

These fixed checks are exact coordinate replay targets. They are not general
theorems about Euclidean geometry.
