# Model

The finite model uses exact rational arithmetic for one linear system:

```text
A = [[2, 1],
     [1, 2]]

b  = [1, 0]
x0 = [0, 0]
```

## Initial Residual

```text
r0 = b - A*x0 = [1, 0]
||r0||_2^2 = 1
```

The one-dimensional Krylov space is spanned by `r0`. The image direction is:

```text
A*r0 = [2, 1]
```

## One-Step GMRES

For `x(alpha) = x0 + alpha*r0`, the residual is:

```text
r(alpha) = b - A*x(alpha)
         = b - alpha*A*r0
```

The squared residual norm is:

```text
||r(alpha)||_2^2
  = (1 - 2*alpha)^2 + (-alpha)^2
  = 1 - 4*alpha + 5*alpha^2
```

The exact minimizer is:

```text
alpha = (b^T A r0) / ((A r0)^T(A r0))
      = 2 / 5
```

So:

```text
x1 = [2/5, 0]
A*x1 = [4/5, 2/5]
r1 = [1/5, -2/5]
||r1||_2^2 = 1/5
```

The orthogonality condition is:

```text
r1^T * (A*r0) = 0
```

The checked QF_LRA artifact isolates only the final scalar contradiction:

```text
gmres_alpha = 2/5
gmres_alpha = 1/2
```
