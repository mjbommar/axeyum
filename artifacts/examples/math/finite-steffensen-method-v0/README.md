# Finite Steffensen Method Checks

This pack records exact rational replay for two finite Steffensen
fixed-point acceleration rows:

```text
x1 = g(x0)
x2 = g(x1)
x_hat = x0 - (x1 - x0)^2 / (x2 - 2*x1 + x0)
```

It checks the fixed arithmetic for:

- an affine half-step map `g(x) = (x + 1)/2` from `x0 = 0`, where the
  accelerated value is the fixed point candidate `1`;
- an affine third-step map `g(x) = 1 + (x - 1)/3` from `x0 = 4`, where the
  accelerated value is also `1`.

The malformed row claims the half-step row's accelerated value is `3/2`.
Exact replay computes `1`, and the checked QF_LRA/Farkas row isolates the
scalar conflict `steffensen_value = 1` and `steffensen_value = 3/2`.

This is not a proof of Steffensen convergence, fixed-point existence,
nonzero-denominator safety for arbitrary iterates, or floating-point
implementation stability.
