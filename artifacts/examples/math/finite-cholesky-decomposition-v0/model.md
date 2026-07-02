# Model

## Fixed Matrices

The source lower-triangular factor is:

```text
L = [ 2  0 ]
    [ 1  3 ]
```

The diagonal entries are positive: `2 > 0` and `3 > 0`. The transpose is:

```text
L^T = [ 2  1 ]
      [ 0  3 ]
```

The product is:

```text
A = L L^T = [ 4   2 ]
            [ 2  10 ]
```

For this fixed two-by-two matrix, the leading principal minors are:

```text
4
4 * 10 - 2 * 2 = 36
```

Both are positive, so this row is a finite positive-definite shadow by
Sylvester's two-by-two criterion. It is not a theorem about arbitrary matrices.

## Malformed Product Entry

The bottom-right product entry is:

```text
1 * 1 + 3 * 3 = 10
```

The malformed row claims the same entry is `9`. The QF_LRA artifact isolates the
final conflict:

```text
cholesky_product_11 = 10
cholesky_product_11 = 9
```

That is a checked finite arithmetic contradiction, not a theorem about all
positive-definite matrices or about numerical Cholesky algorithms.
