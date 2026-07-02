# Calculus Theorem Boundary

This page separates Axeyum's finite calculus resources from general
derivative, integral, multivariable, and manifold-calculus theorem claims.

Primary packs:

- [calculus-algebraic-shadow-v0](../../../artifacts/examples/math/calculus-algebraic-shadow-v0/)
- [calculus-riemann-sum-v0](../../../artifacts/examples/math/calculus-riemann-sum-v0/)
- [multivariable-calculus-rational-v0](../../../artifacts/examples/math/multivariable-calculus-rational-v0/)

Companion lessons and maps:

- [End To End: Finite Calculus Shadows](calculus-shadows-end-to-end.md)
- [End To End: Rational Multivariable Calculus](multivariable-calculus-end-to-end.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)
- [Root-Finding Convergence Theorem Boundary](root-finding-convergence-theorem-boundary.md)
- [Euler Method Theorem Boundary](euler-method-theorem-boundary.md)

## Current Finite Resources

The one-variable algebraic pack works over exact polynomial coefficient lists.
For example:

```text
polynomial = [1, -2, 0, 1]      # 1 - 2*x + x^3
derivative = [-2, 0, 3]         # -2 + 3*x^2
```

It also fixes a product-rule instance:

```text
f = x^2
g = x + 1
(f*g)' = f'*g + f*g' = [0, 2, 3]
```

and fixed tangent/critical-point rows:

```text
p(x) = x^2, point = 3, target = 4
p(3) = 9, p'(3) = 6, tangent value = 15

p(x) = (x - 2)^2 + 1
p'(2) = 0, p''(2) = 2, p(2) = 1
```

The finite Riemann-sum pack fixes rational partitions and polynomial values.
For `f(x) = x` on `[0,1]` with partition `0,1/4,1/2,3/4,1`, it recomputes:

```text
left sum       = 3/8
right sum      = 5/8
trapezoid sum  = 1/2
exact integral = 1/2
```

It also checks midpoint exactness for one affine function, an antiderivative
endpoint row for `2*x`, and lower/upper sums for `x^2` on a two-cell
partition.

The multivariable pack fixes bivariate polynomial and matrix data:

```text
f(x,y) = x^2 + 2xy + 3y^2 + x
point  = (1,2)
value  = 18
grad   = (7,14)
direction = (3,-1)
directional derivative = 7
hessian = [[2,2],[2,6]]
leading minor = 2, determinant = 8
```

It also fixes one polynomial-map chain-rule row:

```text
g(u,v) = (u + v, u - v)
h(x,y) = (x^2 + y, xy)
J_(h o g)(2,1) = J_h(g(2,1)) * J_g(2,1)
               = [[7, 5], [4, -2]]
```

All of these are exact finite algebraic rows. They are useful examples and
regression seeds, but they do not prove analytic calculus theorems.

## Claim And Evidence Rows

| Pack | Check | Expected | Evidence Status | What It Means |
|---|---|---|---|---|
| `calculus-algebraic-shadow-v0` | `polynomial-derivative-coefficients` | `sat` | replay-only | The fixed coefficient-list derivative is recomputed. |
| `calculus-algebraic-shadow-v0` | `product-rule-polynomial-identity` | `sat` | checked | A fixed polynomial product-rule identity is checked by exact coefficient arithmetic. |
| `calculus-algebraic-shadow-v0` | `tangent-line-value-witness` | `sat` | replay-only | The listed tangent-line value for `x^2` is recomputed. |
| `calculus-algebraic-shadow-v0` | `convex-quadratic-critical-point` | `sat` | replay-only | The fixed critical point, value, and second derivative are replayed. |
| `calculus-algebraic-shadow-v0` | `false-derivative-value-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects `derivative_value = 5` after replay computes `6`. |
| `calculus-algebraic-shadow-v0` | `general-calculus-lean-horizon` | `not-run` | lean-horizon | Differentiability from limits, MVT, integration, and FTC remain theorem work. |
| `calculus-riemann-sum-v0` | `riemann-sums-linear-partition` | `sat` | checked | The fixed left/right/trapezoid sums for `f(x)=x` are recomputed. |
| `calculus-riemann-sum-v0` | `midpoint-rule-affine-exact` | `sat` | checked | A fixed affine midpoint-rule sum is recomputed exactly. |
| `calculus-riemann-sum-v0` | `antiderivative-endpoint-replay` | `sat` | checked | The endpoint difference of `x^2` from `1` to `3` is replayed for `2*x`. |
| `calculus-riemann-sum-v0` | `monotone-quadratic-lower-upper-bounds` | `sat` | checked | Lower and upper sums for a fixed monotone quadratic partition are recomputed. |
| `calculus-riemann-sum-v0` | `false-integral-claim-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects `integral_value = 3/4` after replay computes `1/2`. |
| `calculus-riemann-sum-v0` | `fundamental-theorem-lean-horizon` | `not-run` | lean-horizon | Riemann integrability, tagged-partition convergence, and FTC remain theorem work. |
| `multivariable-calculus-rational-v0` | `gradient-at-point-replay` | `sat` | replay-only | The fixed bivariate gradient and value are recomputed. |
| `multivariable-calculus-rational-v0` | `directional-derivative-dot-product` | `sat` | checked | The fixed directional derivative is checked as a gradient dot product. |
| `multivariable-calculus-rational-v0` | `jacobian-chain-rule-replay` | `sat` | checked | A fixed polynomial-map Jacobian chain-rule matrix product is replayed. |
| `multivariable-calculus-rational-v0` | `hessian-positive-definite-replay` | `sat` | checked | The fixed Hessian and Sylvester minors are recomputed. |
| `multivariable-calculus-rational-v0` | `bad-gradient-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects gradient component `13` after replay computes `14`. |
| `multivariable-calculus-rational-v0` | `general-multivariable-calculus-lean-horizon` | `not-run` | lean-horizon | Fréchet differentiability, inverse/implicit function theorems, and manifold calculus remain theorem work. |

The checked rows are exact polynomial, matrix, finite-sum, or scalar
contradiction checks. They are not proofs of derivative rules from limits,
continuity, Riemann integrability, convergence of arbitrary sums, general
chain rules over normed spaces, or the fundamental theorem of calculus.

## What Is Not Proved Yet

The current calculus resources do not prove:

- the limit definition of derivative or differentiability on intervals;
- continuity, IVT, Rolle's theorem, or the mean value theorem;
- power/product/chain rules as general analytic theorems;
- general Riemann or Lebesgue integrability;
- convergence of arbitrary tagged partitions, refinements, or mesh limits;
- the fundamental theorem of calculus;
- uniform convergence, dominated convergence, or interchange of limits;
- Fréchet differentiability over normed vector spaces;
- inverse or implicit function theorems;
- manifold calculus, differential forms, Stokes' theorem, or coordinate-free
  change-of-variables;
- floating-point calculus, automatic-differentiation implementation behavior,
  numerical quadrature stability, or error bounds.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite rows are
exact algebraic shadows and regression seeds, not theorem evidence for general
analysis.

## Query The Boundary

Find calculus theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text calculus \
  --require-any
```

Find the explicit Lean-horizon rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack calculus-algebraic-shadow-v0 \
  --proof-status lean-horizon \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack calculus-riemann-sum-v0 \
  --proof-status lean-horizon \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack multivariable-calculus-rational-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack calculus-algebraic-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack calculus-riemann-sum-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack multivariable-calculus-rational-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked malformed calculus rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack calculus-algebraic-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --text derivative \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack calculus-riemann-sum-v0 \
  --route Farkas \
  --proof-status checked \
  --text integral \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack multivariable-calculus-rational-v0 \
  --route Farkas \
  --proof-status checked \
  --text gradient \
  --require-any
```

## Graduation Criteria

General calculus resources graduate only when they add:

1. precise Lean theorem statements for derivative rules, MVT, Riemann or
   Lebesgue integration, FTC, multivariable chain rules, inverse/implicit
   function theorems, and change-of-variables;
2. explicit hypotheses for domains, intervals, continuity, differentiability,
   compactness, partitions, mesh limits, normed spaces, invertible derivatives,
   and coordinate charts;
3. no-`sorry` proofs with an axiom audit;
4. finite calculus packs linked as examples and regression seeds, not as proof
   evidence for the theorem;
5. separate numerical-honesty metadata for floating-point differentiation,
   quadrature, automatic differentiation, or implementation claims;
6. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, calculus rows remain bounded/computable resources:

```text
untrusted fast search -> proposed derivative table, finite partition, Jacobian, Hessian, or malformed claim
trusted small checking -> exact polynomial/matrix/sum replay and Farkas evidence
theorem horizon       -> differentiability, integrability, FTC, multivariable, and manifold calculus
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/calculus-algebraic-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/calculus-riemann-sum-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/multivariable-calculus-rational-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text calculus --require-any
python3 scripts/query-foundational-resources.py checks --pack calculus-algebraic-shadow-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack calculus-riemann-sum-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack multivariable-calculus-rational-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack calculus-algebraic-shadow-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack calculus-riemann-sum-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack multivariable-calculus-rational-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite packs validate, the
`horizon-frontier` query shows checked finite shadows, and the calculus theorem
rows remain `lean-horizon`.
