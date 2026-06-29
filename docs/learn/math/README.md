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
| [Logic And Proof](logic-and-proof.md) | `curriculum_propositional_logic`, `curriculum_predicate_logic`, `curriculum_proof_methods`, `curriculum_induction`, `field_logic_and_proof` | `logic-basics-v0`, `finite-predicate-v0`, `proof-methods-refutation-v0`, `induction-obligations-v0`, `graph-coloring-v0` |
| [Sets, Relations, And Finite Structures](sets-relations-and-finite-structures.md) | `curriculum_sets`, `curriculum_relations_and_functions`, `curriculum_cardinality`, `field_set_theory_and_foundations` | `finite-sets-v0`, `relations-functions-v0`, `finite-cardinality-v0`, `finite-topology-v0`, `finite-compactness-v0`, `finite-connectedness-v0`, `finite-continuous-maps-v0` |
| [Number Systems And Arithmetic](number-systems-and-arithmetic.md) | `curriculum_naturals`, `curriculum_integers`, `curriculum_divisibility_and_euclid`, `curriculum_modular_arithmetic`, `curriculum_number_theory`, `curriculum_rationals`, `curriculum_complex` | `natural-arithmetic-v0`, `integer-lia-v0`, `gcd-bezout-v0`, `modular-arithmetic-v0`, `number-theory-v0`, `rationals-lra-v0`, `complex-algebraic-v0` |
| [Algebra And Number Theory](algebra-and-number-theory.md) | `field_abstract_algebra`, `field_number_theory` | `gcd-bezout-v0`, `number-theory-v0`, `finite-groups-v0`, `finite-rings-v0`, `finite-fields-v0` |
| [Rational And Real Algebra](rational-real-algebra.md) | `field_real_analysis`, `curriculum_reals` | `rationals-lra-v0`, `reals-rcf-shadow-v0`, `polynomial-identities-v0`, `matrix-invariants-v0`, `linear-optimization-v0` |
| [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md) | `field_graph_theory`, `field_discrete_math` | `counting-v0`, `graph-coloring-v0`, `graph-reachability-v0`, `graph-search-runtime-v0`, `graph-matching-v0`, `graph-d-separation-v0`, `graph-cut-v0`, `proof-methods-refutation-v0` |
| [Linear Algebra And Optimization](linear-algebra-and-optimization.md) | `curriculum_linear_algebra`, `field_optimization_and_convexity` | `linear-algebra-rational-v0`, `numerical-linear-algebra-v0`, `spectral-linear-algebra-v0`, `matrix-invariants-v0`, `random-matrix-finite-v0`, `linear-optimization-v0`, `finite-operator-v0`, `finite-chebyshev-systems-v0` |
| [Probability And Statistics](probability-and-statistics.md) | `field_probability_theory`, `field_statistics` | `finite-probability-v0`, `finite-random-variables-v0`, `finite-conditional-expectation-v0`, `finite-stochastic-kernels-v0`, `finite-hitting-times-v0`, `finite-concentration-v0`, `finite-martingales-v0`, `finite-integration-v0`, `finite-product-measure-v0`, `finite-markov-chain-v0`, `descriptive-statistics-v0`, `exact-statistical-tests-v0`, `finite-measure-v0`, `random-matrix-finite-v0` |
| [Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md) | `field_topology`, `field_measure_theory`, `field_functional_analysis_and_operator_theory` | `sequence-limit-shadow-v0`, `metric-continuity-v0`, `finite-compactness-v0`, `finite-connectedness-v0`, `finite-continuous-maps-v0`, `finite-integration-v0`, `finite-product-measure-v0`, `calculus-algebraic-shadow-v0`, `finite-topology-v0`, `bounded-dynamics-v0`, `finite-markov-chain-v0`, `finite-hitting-times-v0`, `finite-operator-v0`, `finite-chebyshev-systems-v0` |

Each cluster page includes an `Encode / Check Walkthrough` section with
validated pack data and the repo-root command that replays it.

## End-To-End Lessons

- [Triangle Coloring](graph-coloring-end-to-end.md): follows a finite graph
  coloring resource from data row through replayed `sat`, checked finite
  `unsat`, and proof/evidence status.
- [Rational Midpoint](rational-midpoint-end-to-end.md): follows an exact
  density witness through fraction arithmetic and replay-only evidence status.
- [Linear System And LP Replay](linear-system-end-to-end.md): follows exact
  matrix replay and a tiny checked Farkas-style LP certificate.
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
