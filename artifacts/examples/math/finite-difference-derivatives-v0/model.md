# Model

All values are exact rationals. A finite-difference row records:

```text
sample_point_i = point + offset_i * step
sample_value_i = polynomial(sample_point_i)
weighted_sum   = sum_i weight_i * sample_value_i
stencil_value  = scale * weighted_sum
exact_value    = d^k polynomial / dx^k at point
```

The pack contains:

- a forward first-difference row for `f(x)=1+3x` at `x=2`, `h=1/2`;
- a central first-difference row for `f(x)=1+2x+x^2` at `x=1`, `h=1/2`;
- a central second-difference row for the same quadratic and point;
- a malformed central first-difference value row claiming `5` where exact
  replay computes `4`.

The checked SMT-LIB artifact only isolates the final scalar contradiction. The
trusted replay of sample points, sample values, weighted terms, scale, stencil
value, and exact derivative value remains in the pack validator.
