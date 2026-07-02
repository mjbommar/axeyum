# Model

The finite model uses exact rational arithmetic over the symmetric matrix:

```text
A = [[2, 1],
     [1, 2]]

q1 = [1, 0]
```

The first Lanczos product and projection are:

```text
A*q1 = [2, 1]
alpha1 = q1^T*A*q1 = 2
v = A*q1 - alpha1*q1 = [0, 1]
beta1 = ||v||_2 = 1
q2 = v / beta1 = [0, 1]
```

The basis is orthonormal:

```text
q1^T*q1 = 1
q2^T*q2 = 1
q1^T*q2 = 0
```

The second step is:

```text
A*q2 = [1, 2]
alpha2 = q2^T*A*q2 = 2
r2 = A*q2 - beta1*q1 - alpha2*q2 = [0, 0]
beta2 = 0
```

For this full two-dimensional basis:

```text
Q = [[1, 0],
     [0, 1]]

T = [[2, 1],
     [1, 2]]

A*Q = Q*T
```

The malformed row claims `beta1 = 2`. Exact replay computes `beta1 = 1`, and
the source SMT-LIB artifact isolates that scalar contradiction for the Farkas
route.
