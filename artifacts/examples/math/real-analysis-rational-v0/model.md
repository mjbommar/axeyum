# Model

All numbers are exact rationals written as strings accepted by Python's
`Fraction` type.

## Interval And Ball

The interval row records:

```text
inner interval = [1/4, 3/4]
outer ball = {x | |x - 1/2| < 1/3}
```

The farthest interval endpoints are `1/4` away from the center, so the closed
interval is contained in the open ball because:

```text
1/4 < 1/3
```

## Linear Epsilon-Delta Slice

The finite continuity row uses:

```text
f(x) = 2x + 1
a = 0
epsilon = 1
delta = 1/2
```

The listed sample points inside the domain ball are:

```text
-1/4, 0, 1/4
```

For each of those points, the validator checks:

```text
|f(x) - f(0)| < 1
```

The bad-delta row reuses the same function but claims `delta = 3/4`. The
counterexample `x = 2/3` satisfies:

```text
|2/3 - 0| = 2/3 < 3/4
|f(2/3) - f(0)| = 4/3 >= 1
```

## Polynomial Side Conditions

The squeeze-style row checks finite samples with `|x| <= 1/10` and verifies:

```text
x^2 <= 1/100
|x^3| <= 1/1000
```

These are exact finite side conditions for teaching, not general limit
theorems.
