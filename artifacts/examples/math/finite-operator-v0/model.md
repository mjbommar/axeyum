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
