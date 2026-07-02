# Model

## Fixed Factorization

The source matrix and factors are:

```text
A = [ 2  1 ]   L = [ 1  0 ]   U = [ 2  1 ]
    [ 4  5 ]       [ 2  1 ]       [ 0  3 ]
```

`L` is unit lower triangular, `U` is upper triangular, and:

```text
L U = [ 1*2 + 0*0   1*1 + 0*3 ]
      [ 2*2 + 1*0   2*1 + 1*3 ]

    = [ 2  1 ]
      [ 4  5 ] = A
```

The determinant and pivot product agree:

```text
det(A) = 2*5 - 1*4 = 6
pivot_product = U[0,0] * U[1,1] = 2 * 3 = 6
```

## Triangular Solve

For `b = [5, 17]`, forward substitution solves `L*y = b`:

```text
y = [5, 7]
```

Back substitution solves `U*x = y`:

```text
x2 = 7/3
x1 = (5 - 7/3) / 2 = 4/3
x = [4/3, 7/3]
```

The validator also checks `A*x = b` exactly.

## Malformed Multiplier

The elimination multiplier is:

```text
l21 = A[1,0] / A[0,0] = 4 / 2 = 2
```

The malformed row claims the same multiplier is `3`. The QF_LRA artifact
isolates the final conflict:

```text
lu_l21 = 2
lu_l21 = 3
```

That is a checked finite arithmetic contradiction, not a theorem about all LU
decompositions or about numerical LU algorithms.
