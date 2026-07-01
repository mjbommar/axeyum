# Model

Lines are represented by exact rational coefficients:

```json
{"a": "2", "b": "-1", "c": "1"}
```

The line equation is:

```text
a*x + b*y + c = 0
```

Points are two-element arrays of exact rational strings:

```json
["3", "7"]
```

## Line Through Two Points

The line:

```text
2x - y + 1 = 0
```

contains `(0,1)` and `(2,5)` because both evaluations are zero.

## Intersection

The lines:

```text
x + y - 3 = 0
x - y - 1 = 0
```

have determinant:

```text
1*(-1) - 1*1 = -2
```

Since the determinant is nonzero, the fixed intersection witness `(2,1)` is
checked by evaluating both line equations at that point.

## Bad Intersection Coordinate Claim

The promoted bad intersection row uses the same two non-parallel lines. Exact
replay checks the intersection point `(2,1)`, while the malformed row claims
the x-coordinate is `3`. The QF_LRA artifact checks only the final coordinate
conflict:

```text
intersection_x = 2
intersection_x = 3
```

## Bad Incidence Claim

The promoted bad row uses the line `2x - y + 1 = 0` and the point `(2,2)`.
Exact replay computes:

```text
2*2 - 2 + 1 = 3
```

The malformed row claims the line value is `0`. The QF_LRA artifact checks only
the final conflict:

```text
line_value = 3
line_value = 0
```

These fixed coordinate checks are finite exact-rational replay targets. They
are not general projective or synthetic geometry theorems.
