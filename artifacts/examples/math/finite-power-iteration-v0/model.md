# Model

The finite model uses exact rational arithmetic.

```text
A = [[2, 0],
     [0, 1]]

v0 = [1, 1]
v1 = A*v0 = [2, 1]
v2 = A*v1 = [4, 1]
```

The pack also records the normalized second iterate:

```text
||v2||_1 = 5
v2 / ||v2||_1 = [4/5, 1/5]
```

For the first iterate `w = [2, 1]`, the Rayleigh quotient is:

```text
A*w = [4, 1]
w^T*A*w = 2*4 + 1*1 = 9
w^T*w = 2*2 + 1*1 = 5
rho(w) = 9/5
```

The finite residual shadow for `lambda = 9/5` is:

```text
A*w - lambda*w = [4, 1] - [18/5, 9/5] = [2/5, -4/5]
||A*w - lambda*w||_infinity = 4/5
```

The exact dominant eigenpair shadow is:

```text
A*[1, 0] = [2, 0] = 2*[1, 0]
```

All rows are fixed-dimension rational replay. They are not a theorem about
general eigensolver convergence or numerical stability.
