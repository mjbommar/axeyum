# Finite Secant Method Checks

This pack records exact rational replay for two finite secant-method steps
applied to:

```text
f(x) = x^2 - 2
```

It checks the fixed arithmetic for:

- the secant step from `x0 = 1`, `x1 = 2`, which computes `next = 4/3`;
- the next secant step from `x0 = 4/3`, `x1 = 3/2`, which computes
  `next = 24/17`;
- the residual decrease on that second fixed step.

The malformed row claims the first secant next value is `3/2`. Exact replay
computes `4/3`, and the checked QF_LRA/Farkas row isolates the scalar conflict
`secant_next = 4/3` and `secant_next = 3/2`.

This is not a proof of secant-method convergence, convergence order,
root existence, denominator safety for arbitrary iterates, bracketing or
globalization behavior, or floating-point implementation stability.
