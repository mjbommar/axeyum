# Model

The checked finite model is one Romberg/Richardson extrapolation step from
composite trapezoid values:

```text
R = (4*T(h/2) - T(h)) / 3
```

For `f(x)=x^2` on `[0,1]`:

```text
T(h)   = (1/2) * (f(0) + f(1)) = 1/2
T(h/2) = (1/2) * (0.5*f(0) + f(1/2) + 0.5*f(1)) = 3/8
R      = (4*(3/8) - 1/2) / 3 = 1/3
exact integral = integral_0^1 x^2 dx = 1/3
```

The finite error cancellation row also checks:

```text
coarse error = 1/2 - 1/3 = 1/6
fine error   = 3/8 - 1/3 = 1/24
ratio        = (1/6) / (1/24) = 4
```

For `f(x)=x^4` on `[0,1]`:

```text
T(h)   = 1/2
T(h/2) = 9/32
R      = (4*(9/32) - 1/2) / 3 = 5/24
exact integral = integral_0^1 x^4 dx = 1/5
residual = 5/24 - 1/5 = 1/120
```

The bad row claims the quadratic Romberg value is `1/4`. Exact replay computes
`1/3`, so the gap is:

```text
1/3 - 1/4 = 1/12
```
