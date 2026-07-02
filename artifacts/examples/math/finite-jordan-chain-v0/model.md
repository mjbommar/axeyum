# Model

The fixed matrix is the rational Jordan block

```text
A = [[2, 1],
     [0, 2]]
```

with eigenvalue

```text
lambda = 2.
```

The nilpotent part is

```text
N = A - lambda*I
  = [[0, 1],
     [0, 0]]
```

and the chain vectors are

```text
v1 = [1, 0]
v2 = [0, 1]
```

The validator checks the eigenvector row:

```text
A*v1 = [2, 0]
lambda*v1 = [2, 0]
```

and the generalized eigenvector row:

```text
N*v2 = [1, 0] = v1
A*v2 = [1, 2] = lambda*v2 + v1
```

The nilpotent replay checks

```text
N^2 = [[0, 0],
       [0, 0]]
N != 0
```

The reconstruction row is intentionally tiny:

```text
P = I
J = [[2, 1],
     [0, 2]]
P^-1 = I
P*J*P^-1 = A
```

The malformed row claims the first component of `N*v2` is `0`, while exact
replay computes `1`.
