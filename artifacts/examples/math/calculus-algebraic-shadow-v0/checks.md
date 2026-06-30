# Checks

| ID | Expected | Trust Status | Route |
|---|---|---|---|
| `polynomial-derivative-coefficients` | `sat` | replay-only | Recompute a polynomial derivative coefficient list. |
| `product-rule-polynomial-identity` | `sat` | checked | Check the product-rule identity for fixed polynomial factors. |
| `tangent-line-value-witness` | `sat` | replay-only | Replay a tangent-line value from `p(a) + p'(a)(x-a)`. |
| `convex-quadratic-critical-point` | `sat` | replay-only | Check derivative zero, positive second derivative, and value at a fixed point. |
| `false-derivative-value-rejected` | `unsat` | checked | Reject a false derivative value at a point by exact evaluation, then check the final contradiction through QF_LRA/Farkas evidence. |
| `general-calculus-lean-horizon` | `not-run` | lean-horizon | Keep analytic calculus theorems out of the algebraic replay claim. |

The checked rows are still algebraic. They do not prove differentiability from
the limit definition or any integration theorem.

The source SMT-LIB artifact records the final exact-rational conflict after
polynomial derivative replay:

```text
derivative_value = 6
derivative_value = 5
```

The `math_resource_lra_routes` regression parses
`smt2/false-derivative-farkas-conflict.smt2`, emits `UnsatFarkas` evidence, and
independently checks the certificate.
