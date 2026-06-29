# Model

Polynomials use coefficient lists in ascending degree order. For example:

```text
[1, -2, 0, 1]  means  1 - 2*x + x^3
```

The derivative operator is the coefficient transformation:

```text
d/dx sum_i c_i*x^i = sum_i i*c_i*x^(i-1)
```

The pack checks:

- derivative coefficients for `1 - 2*x + x^3`;
- the product rule for `x^2 * (x + 1)`;
- the tangent line to `x^2` at `x = 3`, evaluated at `x = 4`;
- the critical point of `(x - 2)^2 + 1`;
- rejection of the false claim that `(x^2)'` at `x = 3` is `5`.

The final row records that analytic calculus theorems are not consequences of
these algebraic checks.
