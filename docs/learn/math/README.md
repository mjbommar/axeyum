# Learn: Mathematics As Checkable Resources

This path connects the university-style math curriculum to Axeyum's resource
packs. It is not a textbook. Each page shows what can be checked today, what
evidence exists, and what remains a proof-assistant or numerical horizon.

Source maps:

- [curriculum DAG](../../curriculum/README.md)
- [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)
- [example-pack inventory](../../foundational-resources/README.md)

## Lesson Paths

| Path | Start With | First Checkable Packs |
|---|---|---|
| [Logic And Proof](logic-and-proof.md) | `curriculum_propositional_logic`, `curriculum_predicate_logic`, `curriculum_proof_methods`, `curriculum_induction`, `field_logic_and_proof` | `logic-basics-v0`, `finite-predicate-v0`, `proof-methods-refutation-v0`, `proof-methods-patterns-v0`, `induction-obligations-v0`, `induction-patterns-v0`, `graph-coloring-v0` |
| [Sets, Relations, And Finite Structures](sets-relations-and-finite-structures.md) | `curriculum_sets`, `curriculum_relations_and_functions`, `curriculum_cardinality`, `field_set_theory_and_foundations` | `finite-sets-v0`, `relations-functions-v0`, `equivalence-classes-v0`, `function-composition-v0`, `finite-monoids-v0`, `finite-permutation-groups-v0`, `finite-group-actions-v0`, `finite-order-lattices-v0`, `finite-cardinality-v0`, `cardinality-principles-v0`, `finite-topology-v0`, `finite-compactness-v0`, `finite-connectedness-v0`, `finite-continuous-maps-v0`, `finite-simplicial-homology-v0` |
| [Number Systems And Arithmetic](number-systems-and-arithmetic.md) | `curriculum_naturals`, `curriculum_integers`, `curriculum_divisibility_and_euclid`, `curriculum_modular_arithmetic`, `curriculum_number_theory`, `curriculum_rationals`, `curriculum_complex` | `natural-arithmetic-v0`, `integer-lia-v0`, `gcd-bezout-v0`, `modular-arithmetic-v0`, `number-theory-v0`, `rationals-lra-v0`, `complex-algebraic-v0` |
| [Algebra And Number Theory](algebra-and-number-theory.md) | `field_abstract_algebra`, `field_number_theory` | `gcd-bezout-v0`, `number-theory-v0`, `finite-groups-v0`, `finite-monoids-v0`, `finite-permutation-groups-v0`, `finite-group-actions-v0`, `finite-rings-v0`, `finite-fields-v0`, `finite-algebra-homomorphisms-v0`, `finite-ideals-v0`, `finite-vector-spaces-v0`, `finite-dual-spaces-v0`, `finite-modules-v0`, `finite-tensor-products-v0`, `polynomial-factorization-rational-v0` |
| [Rational And Real Algebra](rational-real-algebra.md) | `field_real_analysis`, `curriculum_reals` | `rationals-lra-v0`, `real-analysis-rational-v0`, `reals-rcf-shadow-v0`, `polynomial-identities-v0`, `polynomial-factorization-rational-v0`, `matrix-invariants-v0`, `multivariable-calculus-rational-v0`, `linear-optimization-v0`, `convexity-rational-v0` |
| [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md) | `field_graph_theory`, `field_discrete_math` | `counting-v0`, `finite-permutation-groups-v0`, `finite-group-actions-v0`, `graph-coloring-v0`, `graph-reachability-v0`, `graph-search-runtime-v0`, `graph-matching-v0`, `graph-d-separation-v0`, `graph-cut-v0`, `proof-methods-refutation-v0` |
| [Linear Algebra And Optimization](linear-algebra-and-optimization.md) | `curriculum_linear_algebra`, `field_optimization_and_convexity` | `linear-algebra-rational-v0`, `finite-vector-spaces-v0`, `finite-dual-spaces-v0`, `inner-product-spaces-rational-v0`, `finite-modules-v0`, `finite-tensor-products-v0`, `numerical-linear-algebra-v0`, `spectral-linear-algebra-v0`, `matrix-invariants-v0`, `random-matrix-finite-v0`, `finite-simplicial-homology-v0`, `multivariable-calculus-rational-v0`, `linear-optimization-v0`, `convexity-rational-v0`, `finite-operator-v0`, `finite-chebyshev-systems-v0` |
| [Probability And Statistics](probability-and-statistics.md) | `field_probability_theory`, `field_statistics` | `finite-probability-v0`, `finite-random-variables-v0`, `finite-conditional-expectation-v0`, `finite-stochastic-kernels-v0`, `finite-hitting-times-v0`, `finite-concentration-v0`, `finite-martingales-v0`, `finite-integration-v0`, `finite-product-measure-v0`, `finite-markov-chain-v0`, `descriptive-statistics-v0`, `exact-statistical-tests-v0`, `finite-measure-v0`, `random-matrix-finite-v0` |
| [Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md) | `field_topology`, `field_measure_theory`, `field_functional_analysis_and_operator_theory` | `real-analysis-rational-v0`, `sequence-limit-shadow-v0`, `metric-continuity-v0`, `finite-compactness-v0`, `finite-connectedness-v0`, `finite-continuous-maps-v0`, `finite-simplicial-homology-v0`, `finite-integration-v0`, `finite-product-measure-v0`, `calculus-algebraic-shadow-v0`, `calculus-riemann-sum-v0`, `multivariable-calculus-rational-v0`, `finite-topology-v0`, `bounded-dynamics-v0`, `finite-markov-chain-v0`, `finite-hitting-times-v0`, `inner-product-spaces-rational-v0`, `finite-operator-v0`, `finite-chebyshev-systems-v0` |

Each cluster page includes an `Encode / Check Walkthrough` section with
validated pack data and the repo-root command that replays it.

## End-To-End Lessons

- [Finite Sets](finite-sets-end-to-end.md): follows finite universe/subset
  replay, union/intersection identity replay, subset transitivity, and a fixed
  malformed-identity rejection.
- [Relations And Functions](relations-functions-end-to-end.md): follows finite
  partial-order replay, bijective function-table replay, and checked rejection
  of a multi-valued graph.
- [Triangle Coloring](graph-coloring-end-to-end.md): follows a finite graph
  coloring resource from data row through replayed `sat`, checked finite
  `unsat`, and proof/evidence status.
- [Rational Midpoint](rational-midpoint-end-to-end.md): follows an exact
  density witness through fraction arithmetic and replay-only evidence status.
- [Linear System And LP Replay](linear-system-end-to-end.md): follows exact
  matrix replay and a tiny checked Farkas-style LP certificate.
- [Rational Inner Product Spaces](inner-product-spaces-end-to-end.md):
  follows exact Gram-matrix replay, fixed Cauchy-Schwarz, orthogonal
  projection, Gram-Schmidt, and checked bad-inner-product rejection.
- [Finite Vector Spaces](finite-vector-spaces-end-to-end.md): follows `F2^2`
  table replay, subspace/span recomputation, linear-map kernel/image replay,
  rank-nullity by finite cardinality, and checked bad-subspace rejection.
- [Finite Dual Spaces](finite-dual-spaces-end-to-end.md): follows covector
  linearity, pointwise dual operations, dual-basis pairing, annihilator replay,
  transpose-map replay, and checked bad-covector rejection.
- [Finite Modules](finite-modules-end-to-end.md): follows `Z/4Z` module-law
  replay, generated submodule replay, multiplication-by-`2` kernel/image,
  quotient-module table replay, and checked bad-submodule rejection.
- [Finite Tensor Products](finite-tensor-products-end-to-end.md): follows
  finite tensor-basis replay, bilinear-map checks, factorization through a
  tensor map, Kronecker-product replay, and checked bad-bilinear rejection.
- [Finite Groups](finite-groups-end-to-end.md): follows `Z/4Z`
  Cayley-table replay, inverse-table replay, and checked rejection of
  subtraction modulo `3` as a group operation.
- [Finite Monoids](finite-monoids-end-to-end.md): follows a two-point
  transformation monoid through function-composition replay, identity and
  associativity checks, unit/idempotent recomputation, and checked
  non-associativity rejection.
- [Finite Permutation Groups](finite-permutation-groups-end-to-end.md):
  follows `S3` point maps through bijection checks, composition-table replay,
  cycle/sign replay, natural action orbit-stabilizer counting, and checked
  bad-nonbijection rejection.
- [Finite Group Actions And Burnside Counting](finite-group-actions-end-to-end.md):
  follows action-law replay, orbit/stabilizer recomputation, Burnside fixed-point
  counting, and checked bad-action rejection.
- [Finite Order Lattices](finite-order-lattices-end-to-end.md): follows finite
  partial-order replay, meet/join recomputation, distributivity checks,
  monotone fixed-point replay, and checked bad-order rejection.
- [Finite Cardinality](finite-cardinality-end-to-end.md): follows finite
  bijection and proper-subset injection witnesses, finite no-injection and
  no-surjection enumeration refutations, and the Cantor Lean horizon.
- [Cardinality Principles](cardinality-principles-end-to-end.md): follows
  inclusion-exclusion, disjoint-union additivity, double-counting, powerset
  cardinality, and an overlapping-set counterexample to false additivity.
- [Finite Rings](finite-rings-end-to-end.md): follows `Z/4Z` ring-table replay,
  zero-divisor witness replay, and checked non-distributive-table rejection.
- [Finite Fields](finite-fields-end-to-end.md): follows `F_7` inverse-table
  replay, exhaustive no-distributivity-counterexample checking in `F_5`, and
  checked no-inverse rejection for `2 mod 6`.
- [Finite Algebra Homomorphisms](finite-algebra-homomorphisms-end-to-end.md):
  follows parity-map preservation, kernel/image recomputation,
  quotient/induced-map replay, ring-homomorphism replay, and checked
  bad-homomorphism rejection.
- [Finite Ideals And Quotient Rings](finite-ideals-quotient-rings-end-to-end.md):
  follows `Z/6Z` ideal closure, principal generation, parity-map kernel/image,
  quotient-ring table replay, and checked bad non-ideal rejection.
- [Conditional Probability, Random Variables, Kernels, Concentration, Martingales, And Product Measures](finite-probability-end-to-end.md):
  follows finite atom tables through exact conditional-probability,
  random-variable, conditional-expectation, finite stochastic-kernel,
  concentration, finite martingale, product-measure, and simple-function
  integral replay.
- [Finite Topology, Maps, Connectedness, And Measure](finite-structures-end-to-end.md):
  follows finite set-family, closure/interior, continuous-map, compactness,
  connectedness, and measure replay.
- [Bounded Dynamics And Operators](analysis-dynamics-end-to-end.md): follows
  bounded recurrence, invariant, operator-bound, Chebyshev recurrence, and
  finite Chebyshev-system replay.

## How To Read These Pages

Use the example packs as the executable source of truth. A lesson can explain a
concept, but a resource only graduates when the pack metadata validates and the
witnesses replay.

The recurring pattern is:

1. Pick a finite, exact, or bounded slice.
2. Encode a tiny claim as data.
3. Replay a model, counterexample, or certificate.
4. Name the horizon honestly when the general theorem needs Lean or a broader
   solver route.
