# Model

The checked finite model is Newton divided differences over exact rationals.
For the quadratic row:

```text
f(x) = 1 + x^2
nodes = 0, 1, 2
values = 1, 2, 5

first differences  = 1, 3
second difference  = 1
Newton coefficients = 1, 1, 1
```

At `x=3`, the Newton basis values are:

```text
1
3 - 0 = 3
(3 - 0) * (3 - 1) = 6
```

So the Newton form evaluates to:

```text
1*1 + 1*3 + 1*6 = 10
```

The cubic row checks one nonzero third divided difference:

```text
f(x) = x^3
nodes = 0, 1, 2, 3
Newton coefficients = 0, 1, 3, 1
evaluation point = 4
Newton terms = 0, 4, 36, 24
interpolated value = 64
```

The bad row claims the quadratic interpolation value at `x=3` is `9`. Exact
replay computes `10`, and the checked SMT-LIB row isolates the contradiction
`interpolated_value = 10` and `interpolated_value = 9`.
