# Model

## Fixed Sample

The source sample has three two-dimensional observations:

```text
X = [ 1  0 ]
    [ 2  1 ]
    [ 4  1 ]
```

The population mean vector is:

```text
mu = [ 7/3  2/3 ]
```

The centered rows are:

```text
X - mu = [ -4/3  -2/3 ]
         [ -1/3   1/3 ]
         [  5/3   1/3 ]
```

The centered Gram matrix is:

```text
(X - mu)^T (X - mu) = [ 14/3  4/3 ]
                      [  4/3  2/3 ]
```

Dividing by the three observations gives the population covariance matrix:

```text
Sigma = [ 14/9  4/9 ]
        [  4/9  2/9 ]
```

For this fixed two-by-two matrix, the leading principal minors are:

```text
14/9
(14/9) * (2/9) - (4/9) * (4/9) = 4/27
```

Both are positive, so this row is a finite exact positive-semidefinite shadow.
It is not a theorem about arbitrary covariance estimators or matrices.

## Malformed Covariance Entry

The off-diagonal covariance entry is:

```text
((-4/3) * (-2/3) + (-1/3) * (1/3) + (5/3) * (1/3)) / 3 = 4/9
```

The malformed row claims the same entry is `1/2`. The QF_LRA artifact isolates
the final conflict:

```text
covariance_01 = 4/9
covariance_01 = 1/2
```

That is a checked finite arithmetic contradiction, not a theorem about all
statistics procedures or covariance algorithms.
