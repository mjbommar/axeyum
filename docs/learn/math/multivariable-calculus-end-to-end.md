# End To End: Rational Multivariable Calculus

This lesson follows one exact multivariable-calculus resource from polynomial
gradient replay to directional derivatives, Jacobian chain rule, Hessian
minors, and a checked bad-gradient rejection. It uses the
[multivariable-calculus-rational-v0](../../../artifacts/examples/math/multivariable-calculus-rational-v0/)
pack.
For the theorem boundary around finite polynomial derivative tables,
Jacobians, Hessians, and general multivariable-calculus horizons, use
[Calculus Theorem Boundary](calculus-theorem-boundary.md).

Concept rows:

- `curriculum_calculus`, `curriculum_polynomials`, `curriculum_reals`, and
  `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_real_analysis`, `field_linear_algebra`,
  `field_optimization_and_convexity`, and `field_numerical_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `gradient-at-point-replay` | `sat` | replay-only |
| `directional-derivative-dot-product` | `sat` | checked |
| `jacobian-chain-rule-replay` | `sat` | checked |
| `hessian-positive-definite-replay` | `sat` | checked |
| `bad-gradient-rejected` | `unsat` | checked |
| `general-multivariable-calculus-lean-horizon` | `not-run` | lean-horizon |

The pack checks fixed bivariate polynomial rows over exact rationals. It does
not claim general differentiability or manifold calculus.

## Replay A Gradient

The quadratic surface is:

```text
f(x,y) = x^2 + 2xy + 3y^2 + x
point = (1,2)
```

The witness records:

```text
f(1,2) = 18
grad f(1,2) = (7,14)
```

The validator differentiates each monomial with respect to `x` and `y`, then
evaluates the derivative polynomials at the point.

## Replay A Directional Derivative

The direction is:

```text
d = (3,-1)
```

The validator checks the dot product:

```text
grad f(1,2) . d = (7,14) . (3,-1) = 7
```

## Replay A Jacobian Chain Rule

The map composition uses:

```text
g(u,v) = (u + v, u - v)
h(x,y) = (x^2 + y, xy)
point = (2,1)
g(point) = (3,1)
```

The validator recomputes:

```text
J_g = [[1,  1],
       [1, -1]]

J_h(g(point)) = [[6, 1],
                 [1, 3]]

J_(h o g)(point) = J_h(g(point)) * J_g
                 = [[7,  5],
                    [4, -2]]
```

This is a fixed polynomial matrix multiplication check.

## Replay Hessian Positive-Definiteness

The Hessian witness is:

```text
H_f = [[2, 2],
       [2, 6]]
leading minor = 2
det(H_f) = 8
```

The validator recomputes the Hessian and checks the two leading principal
minors are positive.

## Reject A Bad Gradient

The bad row claims:

```text
grad f(1,2) = (7,13)
```

The validator recomputes the gradient as `(7,14)` and rejects the false second
component.

The source SMT-LIB artifact
`artifacts/examples/math/multivariable-calculus-rational-v0/smt2/bad-gradient-farkas-conflict.smt2`
checks the final exact-rational conflict:

```text
gradient_y = 14
gradient_y = 13
```

Axeyum emits and independently checks `UnsatFarkas` evidence for that
actual-vs-claimed component contradiction.

## Name The Lean Horizon

The final row records the theorem-prover boundary:

```text
Fréchet differentiability
chain rule over normed spaces
inverse function theorem
implicit function theorem
manifold calculus
```

Those require Lean modules or another kernel-checked proof route. The pack only
checks finite polynomial derivative certificates.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/multivariable-calculus-rational-v0
cargo test -p axeyum-solver --test math_resource_lra_routes multivariable_calculus_bad_gradient_artifact_emits_checked_farkas
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current multivariable-calculus resource pattern:

```text
untrusted fast search -> derivative table, Jacobian, Hessian, or counterexample
trusted small checking -> exact rational polynomial and matrix replay plus Farkas evidence for the final bad-gradient contradiction
remaining horizon -> analytic differentiability and manifold proof routes
```

The graduation route is deterministic exact-rational polynomial obligations
plus checked Farkas certificates for exact-linear bad derivative rows.

For a second-order optimization trace that reuses exact gradient and Hessian
replay in a finite Newton linear solve, read
[End To End: Finite Newton Step](newton-step-end-to-end.md).
