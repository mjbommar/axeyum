# Calculus Theorem Boundary

This page separates Axeyum's finite calculus resources from general
derivative, integral, multivariable, and manifold-calculus theorem claims.

Primary packs:

- [calculus-algebraic-shadow-v0](../../../artifacts/examples/math/calculus-algebraic-shadow-v0/)
- [calculus-riemann-sum-v0](../../../artifacts/examples/math/calculus-riemann-sum-v0/)
- [finite-simpson-rule-v0](../../../artifacts/examples/math/finite-simpson-rule-v0/)
- [finite-divided-differences-v0](../../../artifacts/examples/math/finite-divided-differences-v0/)
- [finite-barycentric-interpolation-v0](../../../artifacts/examples/math/finite-barycentric-interpolation-v0/)
- [finite-difference-derivatives-v0](../../../artifacts/examples/math/finite-difference-derivatives-v0/)
- [finite-taylor-polynomials-v0](../../../artifacts/examples/math/finite-taylor-polynomials-v0/)
- [multivariable-calculus-rational-v0](../../../artifacts/examples/math/multivariable-calculus-rational-v0/)

Companion lessons and maps:

- [End To End: Finite Calculus Shadows](calculus-shadows-end-to-end.md)
- [End To End: Finite Simpson Rule](simpson-rule-end-to-end.md)
- [End To End: Finite Divided Differences](divided-differences-end-to-end.md)
- [End To End: Finite Barycentric Interpolation](barycentric-interpolation-end-to-end.md)
- [End To End: Finite Difference Derivatives](finite-difference-derivatives-end-to-end.md)
- [End To End: Finite Taylor Polynomials](taylor-polynomials-end-to-end.md)
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

The finite Simpson-rule pack fixes exact single-panel quadrature data. For
`f(x)=x^3` on `[0,2]`, it recomputes:

```text
nodes          = 0, 1, 2
weights        = 1, 4, 1
sample values  = 0, 1, 8
weighted sum   = 12
Simpson value  = 4
exact integral = 4
```

It repeats the replay for `1+x^2` on the same interval and isolates the bad
claim `Simpson value = 7/2` as a checked QF_LRA/Farkas scalar conflict.

The finite divided-difference pack fixes exact Newton interpolation data. For
`f(x)=1+x^2` at nodes `0,1,2`, it recomputes:

```text
sample values       = 1, 2, 5
divided differences = [1,2,5], [1,3], [1]
Newton coefficients = 1, 1, 1
basis at x=3        = 1, 3, 6
interpolated value  = 10
```

It repeats the replay for `x^3` at nodes `0,1,2,3` and isolates the bad claim
`interpolated_value = 9` as a checked QF_LRA/Farkas scalar conflict.

The finite-difference derivative pack fixes exact stencil rows. For
`f(x)=1+2x+x^2`, `x=1`, and `h=1/2`, it recomputes:

```text
central first difference  = (f(3/2) - f(1/2)) / 1 = 4
central second difference = (f(1/2) - 2f(1) + f(3/2)) / (1/2)^2 = 2
```

It also checks a forward first-difference row for `1+3x` and isolates the bad
claim `finite_difference_value = 5` as a checked QF_LRA/Farkas scalar conflict.

The finite Taylor-polynomial pack fixes exact derivative, factorial,
coefficient, basis, and value rows. For `f(x)=1+2x+x^2`, center `1`, and
`x=3/2`, it recomputes:

```text
f(1), f'(1), f''(1) = 4, 4, 2
Taylor coefficients = 4, 4, 1
basis powers        = 1, 1/2, 1/4
Taylor value        = 25/4
polynomial value    = 25/4
```

It also checks `1+x+x^2+x^3` at center `0`, records a degree-1 truncation with
exact remainder `1/4`, and isolates the bad exact claim
`taylor_value = 6` as a checked QF_LRA/Farkas scalar conflict.

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
| `finite-simpson-rule-v0` | `simpson-cubic-exact-witness` | `sat` | replay-only | The listed single-panel Simpson value for `x^3` on `[0,2]` is replayed exactly. |
| `finite-simpson-rule-v0` | `simpson-quadratic-exact-witness` | `sat` | replay-only | A second single-panel Simpson value for `1+x^2` on `[0,2]` is replayed exactly. |
| `finite-simpson-rule-v0` | `bad-simpson-value-rejected` | `unsat` | replay-only | Exact replay rejects the malformed value `7/2` after computing `4`. |
| `finite-simpson-rule-v0` | `qf-lra-bad-simpson-value` | `unsat` | checked | A QF_LRA/Farkas row checks the scalar contradiction `simpson_value = 4` and `simpson_value = 7/2`. |
| `finite-simpson-rule-v0` | `general-simpson-rule-theory-lean-horizon` | `not-run` | lean-horizon | Degree-of-exactness, composite/adaptive quadrature convergence, error terms, and floating-point quadrature remain theorem/numerical-honesty work. |
| `finite-divided-differences-v0` | `quadratic-divided-difference-table` | `sat` | replay-only | The listed Newton table for `1+x^2` at nodes `0,1,2` is replayed exactly. |
| `finite-divided-differences-v0` | `quadratic-newton-evaluation-witness` | `sat` | replay-only | The Newton form from the quadratic table evaluates to `10` at `x=3`. |
| `finite-divided-differences-v0` | `cubic-divided-difference-table` | `sat` | replay-only | The listed Newton table for `x^3` at nodes `0,1,2,3` is replayed exactly. |
| `finite-divided-differences-v0` | `bad-interpolation-value-rejected` | `unsat` | replay-only | Exact replay rejects the malformed value `9` after computing `10`. |
| `finite-divided-differences-v0` | `qf-lra-bad-interpolation-value` | `unsat` | checked | A QF_LRA/Farkas row checks the scalar contradiction `interpolated_value = 10` and `interpolated_value = 9`. |
| `finite-divided-differences-v0` | `general-interpolation-theory-lean-horizon` | `not-run` | lean-horizon | Interpolation uniqueness, error estimates, conditioning, splines, and floating-point interpolation remain theorem/numerical-honesty work. |
| `finite-barycentric-interpolation-v0` | `linear-barycentric-evaluation-witness` | `sat` | replay-only | The listed barycentric weights and value for `1+2*x` at nodes `0,2` are replayed exactly. |
| `finite-barycentric-interpolation-v0` | `quadratic-barycentric-evaluation-witness` | `sat` | replay-only | Nonuniform-node barycentric weights for `x^2` at nodes `0,1,3` evaluate to `4` at `x=2`. |
| `finite-barycentric-interpolation-v0` | `node-hit-barycentric-witness` | `sat` | replay-only | The node-hit case returns the exact sample value instead of evaluating the removable singularity quotient. |
| `finite-barycentric-interpolation-v0` | `bad-barycentric-value-rejected` | `unsat` | replay-only | Exact replay rejects the malformed value `5` after computing `4`. |
| `finite-barycentric-interpolation-v0` | `qf-lra-bad-barycentric-value` | `unsat` | checked | A QF_LRA/Farkas row checks the scalar contradiction `barycentric_value = 4` and `barycentric_value = 5`. |
| `finite-barycentric-interpolation-v0` | `general-barycentric-interpolation-theory-lean-horizon` | `not-run` | lean-horizon | Barycentric/Lagrange/Newton equivalence, error, conditioning, Runge, spline, and floating-point interpolation theory remain theorem/numerical-honesty work. |
| `finite-difference-derivatives-v0` | `forward-difference-affine-exact-witness` | `sat` | replay-only | The listed forward first-difference stencil for `1+3*x` is replayed exactly. |
| `finite-difference-derivatives-v0` | `central-difference-quadratic-exact-witness` | `sat` | replay-only | The listed central first-difference stencil for `1+2*x+x^2` evaluates to `4`. |
| `finite-difference-derivatives-v0` | `second-central-difference-quadratic-exact-witness` | `sat` | replay-only | The listed central second-difference stencil for the same quadratic evaluates to `2`. |
| `finite-difference-derivatives-v0` | `bad-finite-difference-value-rejected` | `unsat` | replay-only | Exact replay rejects the malformed value `5` after computing `4`. |
| `finite-difference-derivatives-v0` | `qf-lra-bad-finite-difference-value` | `unsat` | checked | A QF_LRA/Farkas row checks the scalar contradiction `finite_difference_value = 4` and `finite_difference_value = 5`. |
| `finite-difference-derivatives-v0` | `general-finite-difference-theory-lean-horizon` | `not-run` | lean-horizon | Truncation error, convergence order, stability, boundary stencils, PDE schemes, and floating-point finite-difference behavior remain theorem/numerical-honesty work. |
| `finite-taylor-polynomials-v0` | `quadratic-taylor-at-one-witness` | `sat` | replay-only | The listed degree-2 Taylor row for `1+2*x+x^2` at center `1` evaluates to `25/4`. |
| `finite-taylor-polynomials-v0` | `cubic-taylor-at-zero-witness` | `sat` | replay-only | The listed degree-3 Taylor row for `1+x+x^2+x^3` at center `0` evaluates to `15`. |
| `finite-taylor-polynomials-v0` | `truncated-linearization-witness` | `sat` | replay-only | A degree-1 Taylor linearization evaluates to `6` and records exact remainder `1/4`. |
| `finite-taylor-polynomials-v0` | `bad-taylor-value-rejected` | `unsat` | replay-only | Exact replay rejects the malformed exact value `6` after computing `25/4`. |
| `finite-taylor-polynomials-v0` | `qf-lra-bad-taylor-value` | `unsat` | checked | A QF_LRA/Farkas row checks the scalar contradiction `taylor_value = 25/4` and `taylor_value = 6`. |
| `finite-taylor-polynomials-v0` | `general-taylor-theory-lean-horizon` | `not-run` | lean-horizon | Taylor theorem, remainder bounds, analytic convergence, smoothness hypotheses, multivariable Taylor, and floating-point Taylor evaluation remain theorem/numerical-honesty work. |
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

The barycentric interpolation pack is deliberately a finite exact-rational
resource: it recomputes weights, quotient terms, node-hit behavior, and one
bad scalar value. It does not claim general interpolation theory or numerical
stability.

The finite-difference derivative pack is likewise a finite exact-rational
resource: it recomputes stencil samples and symbolic derivative values. It
does not claim Taylor-error, convergence-order, stability, PDE, boundary, or
floating-point finite-difference theory.

The finite Taylor-polynomial pack is also finite exact-rational replay: it
recomputes derivative samples, factorials, coefficients, basis powers, values,
and one explicit truncated remainder. It does not claim Taylor theorem,
remainder-bound, convergence, smoothness, multivariable, or floating-point
Taylor theory.

## What Is Not Proved Yet

The current calculus resources do not prove:

- the limit definition of derivative or differentiability on intervals;
- continuity, IVT, Rolle's theorem, or the mean value theorem;
- power/product/chain rules as general analytic theorems;
- general Riemann or Lebesgue integrability;
- convergence of arbitrary tagged partitions, refinements, or mesh limits;
- general Simpson or Newton-Cotes exactness, composite/adaptive quadrature
  convergence, or quadrature error bounds;
- general polynomial interpolation uniqueness, divided-difference identities,
  barycentric/Lagrange/Newton equivalence, interpolation error estimates,
  node-choice conditioning, Runge phenomena, spline theory, or floating-point
  interpolation correctness;
- general finite-difference stencil exactness classes, Taylor truncation-error
  bounds, convergence order, stability, boundary-condition handling, PDE
  discretization correctness, automatic-differentiation implementation
  behavior, or floating-point derivative accuracy;
- Taylor theorem hypotheses, Lagrange/integral/Peano/asymptotic remainder
  formulas, analytic convergence, radius-of-convergence, approximation
  error bounds, multivariable Taylor theorem variants, or floating-point
  Taylor-series evaluation accuracy;
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
  --pack finite-simpson-rule-v0 \
  --proof-status lean-horizon \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-divided-differences-v0 \
  --proof-status lean-horizon \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-difference-derivatives-v0 \
  --proof-status lean-horizon \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-taylor-polynomials-v0 \
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
  --pack finite-simpson-rule-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-divided-differences-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-difference-derivatives-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-taylor-polynomials-v0 \
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
  --pack finite-simpson-rule-v0 \
  --route Farkas \
  --proof-status checked \
  --text simpson \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-divided-differences-v0 \
  --route Farkas \
  --proof-status checked \
  --text interpolation \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-difference-derivatives-v0 \
  --route Farkas \
  --proof-status checked \
  --text finite-difference \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-taylor-polynomials-v0 \
  --route Farkas \
  --proof-status checked \
  --text Taylor \
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
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simpson-rule-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-divided-differences-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-barycentric-interpolation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-difference-derivatives-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-taylor-polynomials-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/multivariable-calculus-rational-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text calculus --require-any
python3 scripts/query-foundational-resources.py checks --pack calculus-algebraic-shadow-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack calculus-riemann-sum-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-simpson-rule-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-divided-differences-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-barycentric-interpolation-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-difference-derivatives-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-taylor-polynomials-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack multivariable-calculus-rational-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack calculus-algebraic-shadow-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack calculus-riemann-sum-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-simpson-rule-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-divided-differences-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-barycentric-interpolation-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-difference-derivatives-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-taylor-polynomials-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack multivariable-calculus-rational-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite packs validate, the
`horizon-frontier` query shows checked finite shadows, and the calculus theorem
rows remain `lean-horizon`.
