# Model

The checked finite model is the exact rational secant update:

```text
x_next = x1 - f(x1) * (x1 - x0) / (f(x1) - f(x0))
```

For `f(x)=x^2-2` with `x0 = 1` and `x1 = 2`:

```text
f(1) = -1
f(2) = 2
value_delta = 2 - (-1) = 3
secant_correction = 2 * (2 - 1) / 3 = 2/3
x_next = 2 - 2/3 = 4/3
f(4/3) = -2/9
```

For the next fixed row with `x0 = 4/3` and `x1 = 3/2`:

```text
f(4/3) = -2/9
f(3/2) = 1/4
value_delta = 1/4 - (-2/9) = 17/36
secant_correction = (1/4) * (1/6) / (17/36) = 3/34
x_next = 3/2 - 3/34 = 24/17
f(24/17) = -2/289
```

The residual row checks only this finite decrease:

```text
|f(24/17)| = 2/289 < 1/4 = |f(3/2)|
```

The bad row claims the first secant value is `3/2`. Exact replay computes
`4/3`, so the gap is:

```text
3/2 - 4/3 = 1/6
```
