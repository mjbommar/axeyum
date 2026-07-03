# Finite Aitken Acceleration Checks

This pack records exact rational replay for two finite Aitken
delta-squared acceleration rows:

```text
s_hat = s0 - (s1 - s0)^2 / (s2 - 2*s1 + s0)
```

It checks the fixed arithmetic for:

- a geometric-error row `[2, 3/2, 5/4]`, where Aitken acceleration recovers
  the exact limit candidate `1`;
- a harmonic-tail row `[2, 3/2, 4/3]`, where the accelerated value is `5/4`
  and the fixed residual against the known target `1` decreases from `1/3` to
  `1/4`.

The malformed row claims the geometric row's accelerated value is `3/2`. Exact
replay computes `1`, and the checked QF_LRA/Farkas row isolates the scalar
conflict `aitken_value = 1` and `aitken_value = 3/2`.

This is not a proof of Aitken convergence acceleration, convergence-order
improvement, nonzero-denominator safety for arbitrary sequences, or
floating-point acceleration stability.
