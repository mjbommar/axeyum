# Model

The finite model uses exact rational arithmetic over the raw reflector vector:

```text
v = [2, 1]
v^T*v = 5
```

The Householder matrix is:

```text
H = I - 2*v*v^T/(v^T*v)
  = [[-3/5, -4/5],
     [-4/5,  3/5]]
```

The reflection is symmetric and orthogonal:

```text
H^T = H
H^T*H = I
H^2 = I
```

The matrix-vector product zeroes the second coordinate:

```text
H*[3,4] = [-5,0]
```

Applying the reflection again reconstructs the original vector:

```text
H*[-5,0] = [3,4]
```

The determinant and norm replay are:

```text
det(H) = -1
||[3,4]||^2 = 25
||H*[3,4]||^2 = 25
```

The malformed row claims `H[0,0] = -4/5`. Exact replay computes
`H[0,0] = -3/5`, and the source SMT-LIB artifact isolates that scalar
contradiction for the Farkas route.
