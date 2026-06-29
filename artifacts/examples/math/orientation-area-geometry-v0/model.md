# Model

Points are two-element arrays of exact rational strings:

```json
["9/4", "3/4"]
```

The signed double area of a triangle `(A, B, C)` is the determinant:

```text
(B_x - A_x) * (C_y - A_y) - (B_y - A_y) * (C_x - A_x)
```

Positive means counterclockwise, negative means clockwise, and zero means
collinear. The ordinary triangle area is half the absolute value.

## Checks

### Triangle Orientation

For `A = (0, 0)`, `B = (4, 0)`, and `C = (1, 3)`:

```text
(4 - 0) * (3 - 0) - (0 - 0) * (1 - 0) = 12
```

The triangle is counterclockwise and has area `6`.

### Affine Area Scaling

The affine map is:

```text
T(x, y) = (2x + y + 1, x + 3y - 1)
```

Its matrix determinant is `5`. The source triangle has signed double area
`12`; its image triangle has signed double area `60`, exactly `5 * 12`.

### Barycentric Point

The point `(9/4, 3/4)` is represented as:

```text
(1/4) * (0, 0) + (1/2) * (4, 0) + (1/4) * (1, 3)
```

The weights are nonnegative and sum to `1`, so this finite row is a point-inside
triangle witness.

### False Orientation

The triangle `(0, 0), (0, 1), (1, 0)` has signed double area `-1`, so the claim
that it is counterclockwise is rejected by exact replay.

The checked linear contradiction is:

```text
signed_double_area = -1
signed_double_area > 0
```

The pack keeps this false fixed-orientation claim on the checked
`UnsatFarkas` route.

These are exact finite replay targets, not a complete formalization of
oriented geometry.
