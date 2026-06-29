# Model

All numbers are exact rationals written as strings accepted by Python's
`Fraction` type.

## Midpoint Convexity

The midpoint row uses:

```text
f(x) = x^2
a = -1
b = 3
m = (a + b) / 2 = 1
```

The validator checks:

```text
f(m) = 1
(f(a) + f(b)) / 2 = (1 + 9) / 2 = 5
1 <= 5
```

## Finite Convex Grid

The grid row lists values of `x^2` on:

```text
-2, -1, 0, 1, 2
```

The validator checks equal spacing and the finite second differences:

```text
4 - 2*1 + 0 = 2
1 - 2*0 + 1 = 2
0 - 2*1 + 4 = 2
```

Each second difference is nonnegative.

## Affine Threshold

The threshold row uses:

```text
g(x) = 3x - 2
x >= 1
```

On the finite samples `1`, `3/2`, and `2`, the outputs are `1`, `5/2`, and
`4`, all at least `1`.

## Bad Midpoint Claim

The bad row documents a finite function:

```text
f(-1) = 0
f(0) = 1
f(1) = 0
```

It fails midpoint convexity because:

```text
f(0) = 1 > (f(-1) + f(1)) / 2 = 0
```

The Axeyum regression checks the same failure in division-free linear form:

```text
left_value = 0
midpoint_value = 1
right_value = 0
2*midpoint_value <= left_value + right_value
```

The final inequality would force `2 <= 0`, so the `QF_LRA` route emits
`UnsatFarkas` evidence and rechecks the certificate independently.
