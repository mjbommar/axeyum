# Model

All vectors, matrices, norms, and polynomial values are exact rational strings.
No floating-point arithmetic or tolerance is used.

## Norm Witness

For:

```text
u = (1, 2)
v = (3, -1)
u + v = (4, 1)
```

the pack checks:

```text
||u||_1 = 3
||v||_1 = 4
||u + v||_1 = 5
5 <= 3 + 4
```

## Operator Bound Witness

For:

```text
A = [[1, -1],
     [2,  1]]
x = (2, -1)
```

the image is:

```text
A*x = (3, 3)
```

The infinity norm of `x` is `2`, the infinity norm of `A*x` is `3`, and the
row-sum norm of `A` is `3`, giving:

```text
||A*x||_infty = 3 <= 3 * 2 = 6
```

The bad-bound row reuses the same exact source object but claims:

```text
||A*x||_infty <= 2
```

Exact replay computes `||A*x||_infty = 3`, so the final inequality is a small
QF_LRA/Farkas contradiction.

The bad `l1` norm row uses the triangle witness but claims:

```text
||u + v||_1 <= 4
```

Exact replay computes `||u+v||_1 = 5`, so the source QF_LRA artifact reduces
the row to:

```text
sum_norm = 5
sum_norm <= 4
```

The Farkas route checks only that final exact linear contradiction.

## Chebyshev Recurrence Witness

For `x = 1/2`, the listed values are:

```text
T0 = 1
T1 = 1/2
T2 = -1/2
T3 = -1
```

The validator checks `T(n+1) = 2*x*T(n) - T(n-1)` for the finite list.

These are finite replay targets, not general operator theory or approximation
theorems.
