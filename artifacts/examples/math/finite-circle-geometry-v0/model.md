# Model

The main witness uses the unit circle centered at the origin:

```text
C = (0,0)
r^2 = 1
P = (3/5,4/5)
```

Exact replay checks:

```text
|P - C|^2 = (3/5)^2 + (4/5)^2 = 1
```

The tangent line at `P` is:

```text
(3/5)x + (4/5)y - 1 = 0
```

The tangent direction is `(-4/5,3/5)`, and the radius vector is `(3/5,4/5)`.
Their dot product is zero.

The chord witness uses the circle `x^2 + y^2 = 25` and endpoints:

```text
A = (3,4)
B = (3,-4)
M = (3,0)
```

The chord direction is `(0,-8)`, the radius to the midpoint is `(3,0)`, and
their dot product is zero.

The bad row uses `Q = (1,1)`. Exact replay computes `|Q|^2 = 2`, while the
malformed row claims `|Q|^2 = 1`.
