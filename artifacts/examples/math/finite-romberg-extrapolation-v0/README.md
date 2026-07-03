# Finite Romberg Extrapolation Checks

This pack records exact rational replay for one finite Romberg/Richardson
extrapolation step built from composite trapezoid values on `[0,1]`.

It checks the fixed arithmetic for:

- `f(x)=x^2`, where one-panel and two-panel trapezoid values extrapolate to
  the exact integral `1/3`;
- the same quadratic row's exact error cancellation;
- `f(x)=x^4`, where the extrapolated value is `5/24` and the finite residual
  against the exact integral `1/5` is `1/120`.

The malformed row claims the quadratic Romberg value is `1/4`. Exact replay
computes `1/3`, and the checked QF_LRA/Farkas row isolates the scalar conflict
`romberg_value = 1/3` and `romberg_value = 1/4`.

This is not a proof of Romberg convergence, Richardson extrapolation theory,
Euler-Maclaurin error expansions, adaptive quadrature correctness, or
floating-point quadrature behavior.
