# Model

The source object is the exact rational quadratic:

```text
f(x, y) = x^2 + 2y^2
```

Equivalently, `f(p) = p^T A p` with:

```text
A = [[1, 0],
     [0, 2]]
```

The committed step starts at:

```text
p0 = (1, 1)
gradient = (2, 4)
alpha = 1/4
p1 = p0 - alpha * gradient = (1/2, 0)
```

The objective values are:

```text
f(p0) = 3
f(p1) = 1/4
decrease = 11/4
```

The finite descent-bound row also records:

```text
||gradient||^2 = 20
alpha/2 * ||gradient||^2 = 5/2
descent slack = 11/4 - 5/2 = 1/4
```

This is a single exact replay check. It does not prove that gradient descent
converges on every smooth convex function, for arbitrary step-size policies, or
under floating-point arithmetic.

The checked bad row changes the claimed decrease to `2`. Exact replay computes
`11/4`, so the claimed decrease has error `3/4`.
