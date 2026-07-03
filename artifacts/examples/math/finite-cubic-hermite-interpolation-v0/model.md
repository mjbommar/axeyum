# Model

Cubic Hermite rows are stored as exact rational endpoint-interpolation replay
obligations. For interval `[a,b]`, endpoint values `y0,y1`, endpoint slopes
`m0,m1`, and evaluation point `x`, the validator recomputes:

```text
h = b - a
t = (x - a) / h
h00 = 2*t^3 - 3*t^2 + 1
h10 = t^3 - 2*t^2 + t
h01 = -2*t^3 + 3*t^2
h11 = t^3 - t^2
H(x) = y0*h00 + h*m0*h10 + y1*h01 + h*m1*h11
```

The listed polynomial must also satisfy the endpoint value and slope
constraints, and `H(x)` must match the polynomial value at the evaluation point.

This model is intentionally finite. It does not encode Hermite interpolation
uniqueness, spline assembly, error formulas, monotonicity guarantees, or
floating-point rounding behavior.
