# Model

All scalar values are exact rationals written as strings accepted by Python's
`Fraction` type. Matrices are row-major arrays of fraction strings; vectors are
arrays of fraction strings.

The pack uses the residual convention:

```text
r = A*x_hat - b
```

and the infinity norm:

```text
||v||_inf = max_i |v_i|
```

No floating-point tolerance is implied. A bound is true only when the exact
rational inequality holds.

## Residual Bound

For

```text
A = [[4, 1],
     [2, 3]]
x_hat = [1, 1]
b = [6, 6]
```

the residual is `[-1, -1]`, so `||r||_inf = 1`.

The checked bad-bound row uses the same replayed residual norm:

```text
residual_inf_norm = 1
residual_inf_norm <= 1/2
```

The pack keeps this false residual-bound claim on the checked `UnsatFarkas`
route.

## Solution Box

For the same system, the exact solution is `[6/5, 6/5]`. The validator checks
both `A*x = b` and the component-wise interval claim:

```text
[1, 1] <= [6/5, 6/5] <= [3/2, 3/2]
```

## Jacobi Step

For

```text
A = [[4, 1],
     [1, 3]]
b = [1, 2]
x0 = [0, 0]
```

the first Jacobi update is `[1/4, 2/3]`. The exact solution is
`[1/11, 7/11]`, the row-sum bound for the Jacobi iteration matrix is `1/3`,
and the validator checks:

```text
||x1 - x*||_inf <= (1/3) * ||x0 - x*||_inf
```

The checked bad-bound row reuses the exact first-step error:

```text
||x1 - x*||_inf = 7/44
||x1 - x*||_inf <= 1/8
```

These fixed checks are finite exact replay targets. They do not yet prove
general convergence or floating-point stability.
