# Model

All values are exact rationals. The regular barycentric evaluator uses

```text
value(x) = sum_i w_i*y_i/(x-x_i) / sum_i w_i/(x-x_i)
w_i      = 1 / product_{j != i} (x_i - x_j)
```

for evaluation points that are not nodes. If the evaluation point is a node,
the resource records a separate node-hit mode and returns the listed sample
value directly.

The pack contains:

- a linear row for `f(x)=1+2x` at nodes `0,2`, evaluated at `x=1`;
- a quadratic row for `f(x)=x^2` at nodes `0,1,3`, evaluated at `x=2`;
- a quadratic node-hit row for the same nodes, evaluated at `x=1`;
- a malformed quadratic value row claiming `5` where exact replay computes `4`.

The checked SMT-LIB artifact only isolates the final scalar contradiction. The
trusted replay of weights, numerator terms, denominator terms, sums, and
node-hit behavior remains in the pack validator.
