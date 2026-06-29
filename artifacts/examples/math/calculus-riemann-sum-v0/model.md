# Model

The pack models finite integration shadows as rational partitions and polynomial
coefficient lists.

Polynomials use the existing low-to-high coefficient convention:

```text
["0", "1"]       means x
["1", "2"]       means 1 + 2*x
["0", "0", "1"]  means x^2
```

For a partition `x_0 < ... < x_n`, the validator computes:

```text
left_sum      = sum f(x_i)     * (x_{i+1} - x_i)
right_sum     = sum f(x_{i+1}) * (x_{i+1} - x_i)
midpoint_sum  = sum f((x_i + x_{i+1}) / 2) * (x_{i+1} - x_i)
trapezoid_sum = sum (f(x_i) + f(x_{i+1})) / 2 * (x_{i+1} - x_i)
```

Exact integrals for polynomial rows are endpoint differences of the computed
antiderivative.

## Limitations

These rows are fixed finite rational calculations. They are useful for teaching
the executable shape of Riemann sums and exact polynomial integration, but they
do not prove that arbitrary Riemann sums converge or that differentiation and
integration are inverse operations in general.
