# Model

The source matrix is:

```text
A = [[4, 2],
     [2, 3]]
```

The block split uses a one-by-one leading block:

```text
B = [[4]]
C^T = [[2]]
C = [[2]]
D = [[3]]
```

The listed inverse of the leading block is:

```text
B^-1 = [[1/4]]
```

Exact block replay gives:

```text
S = D - C*B^-1*C^T
  = 3 - 2*(1/4)*2
  = 2
```

The determinant row checks the block determinant identity for this fixed split:

```text
det(A) = 4*3 - 2*2 = 8
det(B) = 4
det(S) = 2
det(B)*det(S) = 8
```

The inverse row checks:

```text
A^-1 = [[ 3/8, -1/4],
        [-1/4,  1/2]]

A*A^-1 = I
A^-1*A = I
```

The positive-definite shadow is the finite one-by-one Schur criterion:

```text
B > 0
S > 0
det(A) > 0
```

The conditional-variance shadow reads the same matrix as a covariance matrix:

```text
Var(X) = 4
Cov(Y,X) = 2
Var(Y) = 3
Var(Y | X) shadow = 3 - 2*(1/4)*2 = 2
```

That is an exact finite table check. General Gaussian conditioning and
statistical conditioning theorems remain outside this resource.
