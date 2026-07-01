# Model

The source object is the one-dimensional constrained quadratic

```text
minimize f(x) = (x - 2)^2 = x^2 - 4x + 4
subject to x <= 1
```

The committed finite grid is `{-1, 0, 1}` with objective values `9`, `4`, and
`1`. The grid row is only a finite replay check; it is not a proof of global
optimality.

The KKT witness is:

```text
x = 1
constraint g(x) = x - 1 = 0
gradient f'(x) = -2
multiplier lambda = 2
stationarity f'(x) + lambda * 1 = 0
complementarity lambda * g(x) = 0
```

The checked bad row changes the multiplier to `1`. Exact replay then computes
`f'(1) + 1 * 1 = -1`, so the claimed stationarity residual `0` has error `1`.

The second checked bad row keeps `x = 1` and `lambda = 2` but claims
complementarity product `1`. Exact replay computes `2 * (1 - 1) = 0`, so the
claimed product has error `1`.
