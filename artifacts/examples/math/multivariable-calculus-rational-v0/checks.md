# Checks

| Check | Result | Evidence |
|---|---|---|
| `gradient-at-point-replay` | `sat` | Recompute polynomial value and both partial derivatives at `(1,2)`. |
| `directional-derivative-dot-product` | `sat` | Recompute `grad f(1,2) · (3,-1) = 7`. |
| `jacobian-chain-rule-replay` | `sat` | Recompute `g(2,1)`, both Jacobians, and the matrix product. |
| `hessian-positive-definite-replay` | `sat` | Recompute the Hessian and check leading principal minors `2` and `8`. |
| `bad-gradient-rejected` | `unsat` | Recompute the gradient as `(7,14)` and reject `(7,13)` with QF_LRA/Farkas evidence for the final component conflict. |
| `general-multivariable-calculus-lean-horizon` | `not-run` | Names the Lean route for general analytic theorems. |

The checked rows are exact finite replay rows, not floating-point numerical
experiments.

The source SMT-LIB artifact records the final exact-rational conflict after
polynomial derivative replay:

```text
gradient_y = 14
gradient_y = 13
```

The `math_resource_lra_routes` regression parses
`smt2/bad-gradient-farkas-conflict.smt2`, emits `UnsatFarkas` evidence, and
independently checks the certificate.
