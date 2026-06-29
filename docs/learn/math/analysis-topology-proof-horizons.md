# Analysis And Topology Proof Horizons

Concept rows:

- `field_topology`, `field_measure_theory`,
  `field_differential_equations_and_dynamical_systems`, and
  `field_functional_analysis_and_operator_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_sequences_and_limits`, `curriculum_calculus`, and
  `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

Example packs:

- [reals-rcf-shadow-v0](../../../artifacts/examples/math/reals-rcf-shadow-v0/)
- [real-analysis-rational-v0](../../../artifacts/examples/math/real-analysis-rational-v0/)
- [sequence-limit-shadow-v0](../../../artifacts/examples/math/sequence-limit-shadow-v0/)
- [generating-functions-v0](../../../artifacts/examples/math/generating-functions-v0/)
- [metric-continuity-v0](../../../artifacts/examples/math/metric-continuity-v0/)
- [finite-compactness-v0](../../../artifacts/examples/math/finite-compactness-v0/)
- [finite-connectedness-v0](../../../artifacts/examples/math/finite-connectedness-v0/)
- [finite-continuous-maps-v0](../../../artifacts/examples/math/finite-continuous-maps-v0/)
- [finite-simplicial-homology-v0](../../../artifacts/examples/math/finite-simplicial-homology-v0/)
- [calculus-algebraic-shadow-v0](../../../artifacts/examples/math/calculus-algebraic-shadow-v0/)
- [calculus-riemann-sum-v0](../../../artifacts/examples/math/calculus-riemann-sum-v0/)
- [multivariable-calculus-rational-v0](../../../artifacts/examples/math/multivariable-calculus-rational-v0/)
- [finite-topology-v0](../../../artifacts/examples/math/finite-topology-v0/)
- [finite-measure-v0](../../../artifacts/examples/math/finite-measure-v0/)
- [finite-integration-v0](../../../artifacts/examples/math/finite-integration-v0/)
- [finite-product-measure-v0](../../../artifacts/examples/math/finite-product-measure-v0/)
- [bounded-dynamics-v0](../../../artifacts/examples/math/bounded-dynamics-v0/)
- [finite-euler-method-v0](../../../artifacts/examples/math/finite-euler-method-v0/)
- [finite-markov-chain-v0](../../../artifacts/examples/math/finite-markov-chain-v0/)
- [finite-hitting-times-v0](../../../artifacts/examples/math/finite-hitting-times-v0/)
- [inner-product-spaces-rational-v0](../../../artifacts/examples/math/inner-product-spaces-rational-v0/)
- [finite-operator-v0](../../../artifacts/examples/math/finite-operator-v0/)
- [finite-chebyshev-systems-v0](../../../artifacts/examples/math/finite-chebyshev-systems-v0/)
- [spectral-linear-algebra-v0](../../../artifacts/examples/math/spectral-linear-algebra-v0/)

## What Axeyum Checks

The checkable slice is finite or bounded: finite topological spaces, exact
metric balls, finite sigma-algebras, exact finite additivity, algebraic real
shadows, finite simple-function integrals, bounded sequence tails and prefixes,
finite product-measure tables, rectangle probabilities, finite Fubini sums,
bounded rational interval/ball inclusions, finite generating-function
coefficient and recurrence-prefix identities, finite epsilon-delta continuity
checks, finite open-cover/subcover checks, finite clopen-subset and open
separation checks, finite continuous-map preimages and homeomorphism checks,
finite simplicial-complex closure, oriented-boundary replay, boundary-matrix
rank checks, fixed Betti-number replay, and bad boundary-sign rejection,
polynomial derivative identities, exact finite Riemann sums, antiderivative
endpoint replay, exact rational gradients, Jacobian chain-rule replay, Hessian
minor checks, bounded recurrence traces, finite invariant witnesses, matrix
operator bounds, explicit Euler-step replay, finite Euler error tables,
bad Euler-step rejection, Chebyshev recurrence values at fixed points,
finite Chebyshev-system interpolation/sign-pattern checks, exact rational
inner-product Gram matrices, fixed Cauchy-Schwarz/projection/Gram-Schmidt
replay, finite stochastic transition systems, finite first-hit distributions,
and expected hitting-time equation checks. The spectral-linear-algebra pack
adds exact finite eigenpair,
orthogonal-eigenbasis, Rayleigh-quotient, and spectral-decomposition replay for
a fixed rational matrix.

This is the useful boundary for learners: Axeyum can check a concrete finite
model and tell you exactly why it passes.

## Encode / Check Walkthrough

For topology, encode a finite space by listing the universe and open sets. In
`finite-topology-v0`, the validator checks that:

```text
universe = {a,b,c}
open_sets = {}, {a}, {a,b}, {a,b,c}
```

contains the empty set and universe, and is closed under pairwise union and
intersection. The closure/interior witness then becomes a finite set
calculation.

For a bounded sequence shadow, encode exact rational values and one fixed
epsilon:

```text
a_n = 1 / (n + 1)
epsilon = 1/3
tail = n = 3..8
```

The `sequence-limit-shadow-v0` validator checks the finite tail only. It also
checks a finite counterexample to a proposed limit, a monotone bounded prefix,
a fixed geometric partial-sum identity, and a finite Cauchy-tail
no-counterexample row.

For a finite generating-function shadow, encode a sequence prefix as a fixed
coefficient list:

```text
F = [0, 1, 1, 2, 3, 5, 8]
(1 - x - x^2)F(x) = x  through degree 6
```

The `generating-functions-v0` validator checks the bounded coefficient identity
only. It also replays coefficient extraction, finite Cauchy convolution, and a
bad convolution coefficient. General recurrence solving, convergence, and
asymptotics remain Lean-horizon.

For a bounded real-analysis shadow, encode exact rational neighborhoods and a
linear epsilon-delta sample:

```text
[1/4, 3/4] inside {x | |x - 1/2| < 1/3}
f(x) = 2*x + 1
epsilon = 1
delta = 1/2
finite domain sample = -1/4, 0, 1/4
```

The `real-analysis-rational-v0` validator checks interval containment, finite
linear epsilon-delta replay, finite polynomial side conditions, and a checked
bad-delta counterexample. It keeps the fully quantified real theorem as a
Lean-horizon row.

For a finite epsilon-delta continuity shadow, encode a rational metric-space
slice and a function table:

```text
p0 = 0, p1 = 1/4, p2 = 1/2, p3 = 1
f(x) = 2*x
epsilon = 1
delta = 1/2
```

The `metric-continuity-v0` validator checks the finite metric table,
pairwise Lipschitz bounds, the `delta`-ball around `p0`, the output
`epsilon`-ball around `f(p0)`, and a checked bad-delta counterexample.

For a finite compactness shadow, encode an explicit finite topology, an open
cover, and a listed subcover:

```text
U = {a,b,c}
cover = {a,b}, {b,c}, {a,c}
subcover = {a,b}, {b,c}
```

The `finite-compactness-v0` validator checks the topology, recomputes cover
unions, enumerates smaller subfamilies for a minimal-subcover claim, checks a
finite-intersection family, and rejects a bad cover that misses a point.

For a finite connectedness shadow, encode a tiny topology and enumerate clopen
subsets:

```text
U = {0,1}
open_sets = {}, {1}, {0,1}
clopen_subsets = {}, {0,1}
```

The `finite-connectedness-v0` validator enumerates every finite subset,
recomputes clopen subsets, checks that the Sierpinski example has no open
separation, and rejects a false connectedness claim for the two-point discrete
topology.

For a finite continuous-map shadow, encode domain and codomain topologies plus
a total map:

```text
open_X = {}, {1}, {0,1}
open_Y = {}, {v}, {u,v}
f(0) = u
f(1) = v
preimage({v}) = {1}
```

The `finite-continuous-maps-v0` validator recomputes preimages of every
codomain open set, checks continuity, checks a finite homeomorphism by
bijectivity plus continuity of the inverse, and rejects a false continuity
claim for the same map into the discrete topology.

For a finite algebraic-topology shadow, encode a simplicial complex as vertices
and non-empty simplices:

```text
vertices = a, b, c
simplices = [a], [b], [c], [a,b], [a,c], [b,c]
cycle = [a,b] - [a,c] + [b,c]
```

The `finite-simplicial-homology-v0` validator checks face closure, recomputes
oriented boundaries, verifies `boundary^2 = 0`, builds exact rational boundary
matrices, checks the three-edge circle has `b0 = 1` and `b1 = 1`, and rejects a
false boundary sign for `[a,b,c]`.

For the algebraic shadow of calculus, encode polynomial coefficients and the
derived coefficient list:

```text
p = 1 - 2*x + x^3
p' = -2 + 3*x^2
```

The `calculus-algebraic-shadow-v0` validator differentiates coefficient lists,
checks a product-rule identity for fixed polynomials, replays a tangent-line
value, checks a convex quadratic critical point, and rejects a false derivative
value.
For a finite Riemann-sum calculus shadow, encode an exact rational partition:

```text
f(x) = x
partition = 0, 1/4, 1/2, 3/4, 1
left_sum = 3/8
right_sum = 5/8
trapezoid_sum = 1/2
```

The `calculus-riemann-sum-v0` validator recomputes left, right, midpoint, and
trapezoid sums, checks polynomial antiderivative endpoint differences, brackets
an exact integral between monotone lower and upper sums, and rejects a false
integral claim.

For a multivariable calculus shadow, encode a bivariate polynomial map and
exact rational derivative data:

```text
f(x,y) = x^2 + 2xy + 3y^2 + x
grad f(1,2) = (7,14)
direction = (3,-1)
directional derivative = 7
```

The `multivariable-calculus-rational-v0` validator recomputes partial
derivatives, checks the directional derivative as a dot product, verifies a
Jacobian chain-rule matrix product for a fixed polynomial map composition, and
checks a positive-definite Hessian by exact minors.

For a finite-dimensional inner-product shadow, encode rational vectors and a
Gram matrix. The `inner-product-spaces-rational-v0` validator recomputes
positive-definite minors, dot products, the fixed Cauchy-Schwarz inequality,
and orthogonal projection residuals:

```text
proj_span((1,1))(2,3) = (5/2, 5/2)
residual = (-1/2, 1/2)
<residual, (1,1)> = 0
```

That gives a checked finite-dimensional shadow for Hilbert projection and
least-squares reasoning without claiming the general infinite-dimensional
theorem.

For dynamics, encode a bounded recurrence trace:

```text
x(0) = 0
x(t+1) = x(t) + 2
trace = 0, 2, 4, 6, 8
```

The validator checks every transition and then checks the invariant
`0 <= x(t) <= 8` over the finite trace.

For a finite Euler-method shadow, encode a step size, time grid, state trace,
and derivative table:

```text
y' = -y
h = 1/2
states = 1, 1/2, 1/4, 1/8
```

The `finite-euler-method-v0` validator checks every update
`y_(n+1) = y_n + h*f(t_n,y_n)`, replays a finite exact-error table for
`y' = 2t` with solution `y = t^2`, checks a nonnegative monotone invariant,
and rejects a bad one-step claim.

For a finite stochastic transition system, encode a row-stochastic matrix and
an initial distribution. The `finite-markov-chain-v0` validator applies exact
row-vector multiplication for a fixed horizon and checks stationary
distributions by recomputing `pi * P`.

For a focused finite Markov-chain trace, read
[End To End: Finite Markov Chains](finite-markov-chain-end-to-end.md).

For a finite hitting-time shadow, encode a target set in a finite transition
matrix. The `finite-hitting-times-v0` validator computes first-hit
probabilities by carrying only non-hit mass forward, then checks absorption
probability and expected hitting-time equations over exact rationals.

For a focused finite hitting-time trace, read
[End To End: Finite Hitting Times](finite-hitting-times-end-to-end.md).

For finite integration, encode a finite atom table and a rational-valued simple
function. The `finite-integration-v0` validator recomputes weighted sums,
indicator integrals, linearity, and a false expectation counterexample using
exact rational arithmetic.

For a finite product-measure shadow, encode two finite probability spaces and a
Cartesian-product table:

```text
P(heads) = 1/2
Q(one) = 1/3
R(heads, one) = 1/6
```

The `finite-product-measure-v0` validator checks every product probability,
rectangle measures, marginals, and equality of the direct finite integral with
both iterated finite sums.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/reals-rcf-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/real-analysis-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/sequence-limit-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/generating-functions-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/metric-continuity-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-compactness-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-connectedness-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-continuous-maps-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-homology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/calculus-algebraic-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/calculus-riemann-sum-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/multivariable-calculus-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-integration-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-product-measure-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-dynamics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-euler-method-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-markov-chain-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-hitting-times-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/inner-product-spaces-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chebyshev-systems-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/spectral-linear-algebra-v0
```

For fuller traces through bounded rational real-analysis evidence,
real-algebra shadow checks, exact multivariable derivative replay, exact
rational inner products, bounded dynamics, and finite-dimensional operator
replay, read
[End To End: Bounded Rational Real Analysis](real-analysis-rational-end-to-end.md),
[End To End: Generating Functions](generating-functions-end-to-end.md),
[End To End: Metric Continuity](metric-continuity-end-to-end.md),
[End To End: Real Algebra RCF Shadow](reals-rcf-shadow-end-to-end.md),
[End To End: Rational Multivariable Calculus](multivariable-calculus-end-to-end.md),
[End To End: Rational Inner Product Spaces](inner-product-spaces-end-to-end.md),
[End To End: Finite Dynamics And Euler Replay](finite-dynamics-euler-end-to-end.md),
[End To End: Bounded Dynamics And Operators](analysis-dynamics-end-to-end.md),
[End To End: Finite Chebyshev Systems](finite-chebyshev-systems-end-to-end.md),
[End To End: Spectral Linear Algebra](spectral-linear-algebra-end-to-end.md),
[End To End: Numerical Linear Algebra](numerical-linear-algebra-end-to-end.md),
[End To End: Finite Compactness](finite-compactness-end-to-end.md),
[End To End: Finite Connectedness](finite-connectedness-end-to-end.md),
[End To End: Finite Continuous Maps](finite-continuous-maps-end-to-end.md),
[End To End: Finite Simplicial Homology](finite-simplicial-homology-end-to-end.md),
[End To End: Finite Integration](finite-integration-end-to-end.md),
[End To End: Finite Product Measure](finite-product-measure-end-to-end.md),
and [End To End: Finite Topology And Measure](finite-topology-measure-end-to-end.md).

## Horizon

General epsilon-delta limits, differentiability from limits, mean value
theorem, fundamental theorem of calculus, Cauchy completeness, monotone
convergence, compactness, connectedness, Lebesgue measure, integration,
convergence theorems, product-measure construction, Fubini/Tonelli, ODE
existence and uniqueness, Banach/Hilbert space
theorems, Hilbert projection/Riesz representation, compact operators,
closed-form generating-function extraction, asymptotic coefficient estimates,
countably infinite Markov chains,
recurrence/transience classifications, optional stopping, mixing-time bounds,
general Chebyshev spaces, homology invariance, exact sequences, homotopy
equivalence, and infinite-dimensional spectral theory remain Lean-horizon
material.
