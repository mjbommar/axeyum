# Model

The finite model is one exact rational symmetric system:

```text
A = [[4, 2],
     [2, 3]]

L = [[1,   0],
     [1/2, 1]]

D = [[4, 0],
     [0, 2]]

L^T = [[1, 1/2],
       [0, 1]]
```

The replayed factorization is:

```text
L*D = [[4, 0],
       [2, 2]]

L*D*L^T = [[4, 2],
           [2, 3]]
```

For the right-hand side:

```text
b = [6, 5]
```

the triangular solve is:

```text
L*z = b      -> z = [6, 2]
D*y = z      -> y = [3/2, 1]
L^T*x = y    -> x = [1, 1]
A*x = b
```

The determinant and positive-definite shadow are fixed finite checks:

```text
det(A) = 8
product(diag(D)) = 4 * 2 = 8
leading principal minors = [4, 8]
```

The malformed row claims `D[1,1] = 3`; exact replay computes `D[1,1] = 2`.
The checked QF_LRA artifact isolates only that final scalar contradiction.
