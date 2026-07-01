# Model

The finite model is a two-variable convex quadratic program:

```text
minimize f(x,y) = (x - 2)^2 + (y - 1)^2
subject to x <= 1
           y >= 0
```

The unconstrained minimizer is `(2,1)`, where the gradient is zero and the
objective value is `0`. That point violates `x <= 1` by one unit, so the active
set fixes the face `x = 1`.

On that face, the free coordinate solve gives `y = 1`, so the active-set
candidate is:

```text
(x,y) = (1,1)
f(1,1) = 1
grad f(1,1) = (-2,0)
```

Using constraints

```text
a = (1,0),  a . z <= 1
b = (0,-1), b . z <= 0   ; this is y >= 0
```

the active multiplier `lambda = 2` and inactive multiplier `mu = 0` satisfy:

```text
grad f(1,1) + lambda*a + mu*b = (0,0)
active slack = 1 - a.(1,1) = 0
inactive slack = 0 - b.(1,1) = 1
lambda * active_slack = 0
mu * inactive_slack = 0
```

The malformed row uses the feasible point `(1,0)` as if it solved the same
active-face subproblem:

```text
grad f(1,0) = (-2,-2)
grad f(1,0) + 2*a + 0*b = (0,-2)
free-coordinate stationarity error = 2
```

The source SMT-LIB row fixes that exact replayed error as `2` while claiming it
is nonpositive, producing a small QF_LRA/Farkas contradiction.

The degenerate active-bound row uses a second two-variable quadratic:

```text
minimize g(x,y) = (x - 1)^2 + y^2
subject to x <= 1
```

The unconstrained minimizer `(1,0)` is feasible and tight on the active bound.
Its gradient is zero, so stationarity forces the active multiplier to be zero:

```text
grad g(1,0) = (0,0)
active normal = (1,0)
lambda = 0
grad g(1,0) + lambda*(1,0) = (0,0)
```

The malformed degenerate row claims `lambda = 1` is also stationary. Exact
replay computes residual `(1,0)` and stationarity error `1`, and the source
SMT-LIB row fixes that error as both `1` and `0`.
