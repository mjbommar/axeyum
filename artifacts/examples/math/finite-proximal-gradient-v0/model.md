# Model

The source object is the exact rational composite objective:

```text
F(x) = f(x) + lambda * |x|
f(x) = 1/2 * (x - 3)^2
lambda = 1
```

The committed proximal-gradient witness starts at:

```text
x0 = 0
f(x0) = 9/2
grad f(x0) = -3
alpha = 1/2
```

The ordinary gradient trial point is:

```text
x_trial = x0 - alpha * grad f(x0)
        = 0 - (1/2) * (-3)
        = 3/2
```

For the L1 proximal operator, the threshold is:

```text
alpha * lambda = 1/2
```

Since `x_trial = 3/2` is positive and larger than the threshold, the
soft-threshold formula gives:

```text
prox_{alpha * lambda |.|}(3/2) = 3/2 - 1/2 = 1
```

The positive-branch optimality residual is:

```text
(prox_x - x_trial) / alpha + lambda
= (1 - 3/2) / (1/2) + 1
= 0
```

The composite objective values are:

```text
F(0) = 9/2 + 0 = 9/2
F(1) = 2 + 1 = 3
decrease = 3/2
```

The checked bad composite-decrease row keeps those start/prox values fixed and
claims decrease `2`. Exact replay computes `9/2 - 3 = 3/2`, leaving error
`1/2`.

The constrained box-plus-L1 witness uses the same smooth objective, step size,
and L1 penalty, but constrains the proximal subproblem to:

```text
0 <= x <= 3/4
```

The ordinary trial point is still `3/2`, and the unconstrained soft-threshold
point is still `1`. The box-constrained proximal point clips to the active
upper bound:

```text
box_prox_x = 3/4
projection distance = 1 - 3/4 = 1/4
```

On the positive L1 branch, the derivative of the proximal subproblem at the
box point is:

```text
(3/4 - 3/2) / (1/2) + 1 = -1/2
```

The upper-bound multiplier is `1/2`, so stationarity is exact:

```text
-1/2 + 1/2 = 0
```

This is a single exact replay check. It does not prove proximal-gradient
convergence, nonsmooth optimality theory, rate bounds, stochastic variants, or
floating-point behavior.

The checked bad row claims that `1/4` satisfies the same positive-branch
optimality equation. Exact replay computes residual `-3/2`, so the required
zero-residual claim is false.

The checked bad composite-decrease row claims decrease `2` from the same exact
composite values. Exact replay computes decrease `3/2`, so the required exact
decrease claim is false by `1/2`.

The checked boxed bad row claims that the unconstrained soft-threshold point
`1` is feasible for the upper bound `3/4`. Exact replay computes a box
violation of `1/4`, so the required nonpositive-violation claim is false.
