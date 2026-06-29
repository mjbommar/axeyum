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

- [finite-topology-v0](../../../artifacts/examples/math/finite-topology-v0/)
- [finite-measure-v0](../../../artifacts/examples/math/finite-measure-v0/)
- [bounded-dynamics-v0](../../../artifacts/examples/math/bounded-dynamics-v0/)
- [finite-operator-v0](../../../artifacts/examples/math/finite-operator-v0/)

## What Axeyum Checks

The checkable slice is finite or bounded: finite topological spaces, exact
metric balls, finite sigma-algebras, exact finite additivity, bounded recurrence
traces, finite invariant witnesses, matrix operator bounds, and Chebyshev
recurrence values at fixed points.

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

For dynamics, encode a bounded recurrence trace:

```text
x(0) = 0
x(t+1) = x(t) + 2
trace = 0, 2, 4, 6, 8
```

The validator checks every transition and then checks the invariant
`0 <= x(t) <= 8` over the finite trace.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-dynamics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
```

For a fuller trace through bounded dynamics and finite-dimensional operator
replay, read [End To End: Bounded Dynamics And Operators](analysis-dynamics-end-to-end.md).

## Horizon

General epsilon-delta limits, compactness, connectedness, Lebesgue measure,
integration, convergence theorems, ODE existence and uniqueness, Banach/Hilbert
space theorems, compact operators, and general Chebyshev spaces remain
Lean-horizon material.
