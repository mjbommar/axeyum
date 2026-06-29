# Checks

| Check | Result | Evidence |
|---|---|---|
| `gradient-at-point-replay` | `sat` | Recompute polynomial value and both partial derivatives at `(1,2)`. |
| `directional-derivative-dot-product` | `sat` | Recompute `grad f(1,2) · (3,-1) = 7`. |
| `jacobian-chain-rule-replay` | `sat` | Recompute `g(2,1)`, both Jacobians, and the matrix product. |
| `hessian-positive-definite-replay` | `sat` | Recompute the Hessian and check leading principal minors `2` and `8`. |
| `bad-gradient-rejected` | `unsat` | Recompute the gradient as `(7,14)` and reject `(7,13)`. |
| `general-multivariable-calculus-lean-horizon` | `not-run` | Names the Lean route for general analytic theorems. |

The checked rows are exact finite replay rows, not floating-point numerical
experiments.
