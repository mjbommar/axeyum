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
| [Logic And Proof](logic-and-proof.md) | `curriculum_proof_methods`, `field_logic_and_proof` | `proof-methods-refutation-v0`, `graph-coloring-v0` |
| [Sets, Relations, And Finite Structures](sets-relations-and-finite-structures.md) | `curriculum_sets`, `field_set_theory_and_foundations` | `finite-topology-v0`, `finite-measure-v0` |
| [Number Systems And Arithmetic](number-systems-and-arithmetic.md) | `curriculum_modular_arithmetic`, `curriculum_rationals`, `curriculum_complex` | `modular-arithmetic-v0`, `rationals-lra-v0`, `complex-algebraic-v0` |
| [Algebra And Number Theory](algebra-and-number-theory.md) | `field_abstract_algebra`, `field_number_theory` | `modular-arithmetic-v0`, `complex-algebraic-v0` |
| [Rational And Real Algebra](rational-real-algebra.md) | `field_real_analysis`, `curriculum_reals` | `rationals-lra-v0`, `linear-optimization-v0`, `coordinate-geometry-v0` |
| [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md) | `field_graph_theory`, `field_discrete_math` | `graph-coloring-v0`, `proof-methods-refutation-v0` |
| [Linear Algebra And Optimization](linear-algebra-and-optimization.md) | `curriculum_linear_algebra`, `field_optimization_and_convexity` | `linear-algebra-rational-v0`, `linear-optimization-v0`, `finite-operator-v0` |
| [Probability And Statistics](probability-and-statistics.md) | `field_probability_theory`, `field_statistics` | `finite-probability-v0`, `descriptive-statistics-v0`, `finite-measure-v0` |
| [Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md) | `field_topology`, `field_measure_theory`, `field_functional_analysis_and_operator_theory` | `finite-topology-v0`, `bounded-dynamics-v0`, `finite-operator-v0` |

Each cluster page includes an `Encode / Check Walkthrough` section with
validated pack data and the repo-root command that replays it.

## End-To-End Lessons

- [Triangle Coloring](graph-coloring-end-to-end.md): follows a finite graph
  coloring resource from data row through replayed `sat`, checked finite
  `unsat`, and proof/evidence status.

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
