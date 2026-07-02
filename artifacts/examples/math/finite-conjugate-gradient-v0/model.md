# Model

The finite model uses exact rational arithmetic.

```text
A = [[4, 1],
     [1, 3]]

b  = [1, 2]
x0 = [0, 0]
```

The initial residual and search direction are:

```text
r0 = b - A*x0 = [1, 2]
p0 = r0
```

The first step computes:

```text
A*p0 = [6, 7]
r0^T*r0 = 5
p0^T*A*p0 = 20
alpha0 = 5/20 = 1/4
x1 = x0 + alpha0*p0 = [1/4, 1/2]
r1 = r0 - alpha0*A*p0 = [-1/2, 1/4]
```

The updated residual is orthogonal to the first search direction:

```text
r1^T*p0 = (-1/2)*1 + (1/4)*2 = 0
```

The next direction is:

```text
r1^T*r1 = 5/16
beta0 = (r1^T*r1) / (r0^T*r0) = 1/16
p1 = r1 + beta0*p0 = [-7/16, 3/8]
```

The two search directions are A-conjugate:

```text
A*p1 = [-11/8, 11/16]
p0^T*A*p1 = 0
```

The second step reaches the exact solution:

```text
p1^T*A*p1 = 55/64
alpha1 = (r1^T*r1) / (p1^T*A*p1) = 4/11
x2 = x1 + alpha1*p1 = [1/11, 7/11]
A*x2 - b = [0, 0]
```

All rows are fixed-dimension rational replay. They are not a theorem about
general Krylov methods, preconditioners, or floating-point CG.
