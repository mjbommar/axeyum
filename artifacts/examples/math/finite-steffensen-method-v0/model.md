# Model

The checked finite model is Steffensen acceleration for a listed fixed-point
map:

```text
g(x)       = slope*x + intercept
x1         = g(x0)
x2         = g(x1)
delta0     = x1 - x0
delta1     = x2 - x1
delta2     = delta1 - delta0
correction = delta0^2 / delta2
x_hat      = x0 - correction
```

For the half-step row:

```text
g(x) = (x + 1)/2
x0 = 0
x1 = 1/2
x2 = 3/4
delta0 = 1/2
delta1 = 1/4
delta2 = -1/4
correction = (1/4) / (-1/4) = -1
x_hat = 0 - (-1) = 1
```

For the third-step row:

```text
g(x) = 1 + (x - 1)/3 = x/3 + 2/3
x0 = 4
x1 = 2
x2 = 4/3
delta0 = -2
delta1 = -2/3
delta2 = 4/3
correction = 4 / (4/3) = 3
x_hat = 4 - 3 = 1
```

The residual row checks only this finite comparison against the listed affine
fixed point `1` for the half-step row:

```text
|g(3/4) - 3/4| = |7/8 - 3/4| = 1/8
|g(1) - 1| = 0
0 < 1/8
```

The bad row claims the half-step accelerated value is `3/2`. Exact replay
computes `1`, so the gap is:

```text
3/2 - 1 = 1/2
```
