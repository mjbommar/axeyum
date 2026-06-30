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

This is a single exact replay check. It does not prove proximal-gradient
convergence, nonsmooth optimality theory, rate bounds, stochastic variants, or
floating-point behavior.

The checked bad row claims that `1/4` satisfies the same positive-branch
optimality equation. Exact replay computes residual `-3/2`, so the required
zero-residual claim is false.
