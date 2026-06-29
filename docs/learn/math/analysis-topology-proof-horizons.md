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
- [sequence-limit-shadow-v0](../../../artifacts/examples/math/sequence-limit-shadow-v0/)
- [metric-continuity-v0](../../../artifacts/examples/math/metric-continuity-v0/)
- [finite-compactness-v0](../../../artifacts/examples/math/finite-compactness-v0/)
- [finite-connectedness-v0](../../../artifacts/examples/math/finite-connectedness-v0/)
- [finite-continuous-maps-v0](../../../artifacts/examples/math/finite-continuous-maps-v0/)
- [calculus-algebraic-shadow-v0](../../../artifacts/examples/math/calculus-algebraic-shadow-v0/)
- [finite-topology-v0](../../../artifacts/examples/math/finite-topology-v0/)
- [finite-measure-v0](../../../artifacts/examples/math/finite-measure-v0/)
- [bounded-dynamics-v0](../../../artifacts/examples/math/bounded-dynamics-v0/)
- [finite-markov-chain-v0](../../../artifacts/examples/math/finite-markov-chain-v0/)
- [finite-operator-v0](../../../artifacts/examples/math/finite-operator-v0/)
- [spectral-linear-algebra-v0](../../../artifacts/examples/math/spectral-linear-algebra-v0/)

## What Axeyum Checks

The checkable slice is finite or bounded: finite topological spaces, exact
metric balls, finite sigma-algebras, exact finite additivity, algebraic real
shadows, bounded sequence tails and prefixes, finite epsilon-delta continuity
checks, finite open-cover/subcover checks, finite clopen-subset and open
separation checks, finite continuous-map preimages and homeomorphism checks,
polynomial derivative identities, bounded recurrence traces, finite invariant
witnesses, matrix operator bounds, Chebyshev recurrence values at fixed points,
and finite stochastic transition systems. The
spectral-linear-algebra pack adds exact finite eigenpair,
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

For dynamics, encode a bounded recurrence trace:

```text
x(0) = 0
x(t+1) = x(t) + 2
trace = 0, 2, 4, 6, 8
```

The validator checks every transition and then checks the invariant
`0 <= x(t) <= 8` over the finite trace.

For a finite stochastic transition system, encode a row-stochastic matrix and
an initial distribution. The `finite-markov-chain-v0` validator applies exact
row-vector multiplication for a fixed horizon and checks stationary
distributions by recomputing `pi * P`.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/reals-rcf-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/sequence-limit-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/metric-continuity-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-compactness-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-connectedness-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-continuous-maps-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/calculus-algebraic-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-dynamics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-markov-chain-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/spectral-linear-algebra-v0
```

For a fuller trace through bounded dynamics and finite-dimensional operator
replay, read [End To End: Bounded Dynamics And Operators](analysis-dynamics-end-to-end.md).

## Horizon

General epsilon-delta limits, differentiability from limits, mean value
theorem, fundamental theorem of calculus, Cauchy completeness, monotone
convergence, compactness, connectedness, Lebesgue measure, integration,
convergence theorems, ODE existence and uniqueness, Banach/Hilbert space
theorems, compact operators, countably infinite Markov chains, mixing-time
bounds, general Chebyshev spaces, and infinite-dimensional spectral theory
remain Lean-horizon material.
