# Model

The source object is the exact rational quadratic:

```text
f(x) = x^2
```

The committed line-search witness starts at:

```text
x0 = 1
gradient = 2
direction = -2
directional derivative = -4
Armijo c = 1/4
```

The first trial step is `alpha = 1`:

```text
x_trial = 1 + 1 * (-2) = -1
f(x_trial) = 1
Armijo rhs = f(1) + c * alpha * directional_derivative = 0
violation = 1 - 0 = 1
```

So the trial step is rejected.

After one backtrack with factor `1/2`, the accepted step is `alpha = 1/2`:

```text
x_accept = 1 + (1/2) * (-2) = 0
f(x_accept) = 0
Armijo rhs = 1/2
slack = 1/2 - 0 = 1/2
```

This is a single exact replay check. It does not prove line-search termination,
Wolfe conditions, convergence rates, or floating-point behavior.

The checked bad row claims the rejected trial step satisfies Armijo. Exact
replay computes violation `1`, so the nonpositive-violation claim is false.
