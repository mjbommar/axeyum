# Model

The checked finite model is the single-panel Simpson rule:

```text
S(f,[a,b]) = ((b-a)/6) * (f(a) + 4*f((a+b)/2) + f(b))
```

For `f(x)=x^3` on `[0,2]`:

```text
nodes         = 0, 1, 2
sample values = 0, 1, 8
weights       = 1, 4, 1
scale         = 1/3
weighted sum  = 0 + 4*1 + 8 = 12
Simpson value = (1/3) * 12 = 4
exact integral = integral_0^2 x^3 dx = 4
```

For `f(x)=1+x^2` on `[0,2]`:

```text
sample values = 1, 2, 5
weighted sum  = 1 + 4*2 + 5 = 14
Simpson value = 14/3
exact integral = integral_0^2 (1+x^2) dx = 14/3
```

The bad row claims the cubic Simpson value is `7/2`. Exact replay computes
`4`, so the gap is:

```text
4 - 7/2 = 1/2
```
