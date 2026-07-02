# Model

The finite model uses exact rational arithmetic over:

```text
A = [[1, 2],
     [3, 4]]

q1 = [1, 0]
```

The first Arnoldi product and projection are:

```text
A*q1 = [1, 3]
h11 = q1^T*A*q1 = 1
v = A*q1 - h11*q1 = [0, 3]
h21 = ||v||_2 = 3
q2 = v / h21 = [0, 1]
```

The basis is orthonormal:

```text
q1^T*q1 = 1
q2^T*q2 = 1
q1^T*q2 = 0
```

The second column is:

```text
A*q2 = [2, 4]
h12 = q1^T*A*q2 = 2
h22 = q2^T*A*q2 = 4
```

For this full two-dimensional basis:

```text
Q = [[1, 0],
     [0, 1]]

H = [[1, 2],
     [3, 4]]

A*Q = Q*H
```

The malformed row claims `h21 = 2`. Exact replay computes `h21 = 3`, and the
source SMT-LIB artifact isolates that scalar contradiction for the Farkas
route.
