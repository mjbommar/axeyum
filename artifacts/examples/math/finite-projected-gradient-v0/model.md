# Model

The source object is the exact rational quadratic:

```text
f(x) = (x - 2)^2 = x^2 - 4x + 4
```

The constraint set is the rational interval:

```text
C = [0, 1]
```

The committed projected-gradient witness starts at the feasible point:

```text
x0 = 0
f(x0) = 4
gradient = -4
step size = 1/2
```

The unconstrained gradient step is:

```text
x_trial = x0 - alpha * gradient
        = 0 - (1/2) * (-4)
        = 2
```

Projecting the trial point onto `[0,1]` gives:

```text
x_projected = 1
projection distance = |2 - 1| = 1
```

The projected point decreases the objective:

```text
f(1) = 1
decrease = 4 - 1 = 3
```

This is a single exact replay check. It does not prove projected-gradient
convergence, rates, active-set identification, proximal variants, stochastic
variants, or floating-point behavior.

The checked bad row claims that `3/2` is a feasible projected point for
`[0,1]`. Exact interval replay rejects that point because `3/2 > 1`.
