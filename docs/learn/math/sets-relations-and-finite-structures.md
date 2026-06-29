# Sets, Relations, And Finite Structures

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`, and
  `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `field_topology` and `field_measure_theory` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)

Example packs:

- [finite-topology-v0](../../../artifacts/examples/math/finite-topology-v0/)
- [finite-measure-v0](../../../artifacts/examples/math/finite-measure-v0/)

## What Axeyum Checks

The current finite-structure path checks set families. The topology pack checks
empty/universe membership, closure under finite unions and intersections,
closure/interior computation, and finite metric balls. The measure pack checks
finite sigma-algebra closure, rational measure tables, finite additivity, and
event/complement identities.

## Encode / Check Walkthrough

For topology, encode only finite sets:

```text
universe = a,b,c
open_sets = {}, {a}, {a,b}, {a,b,c}
subset = {b}
```

The validator checks the topology axioms and recomputes `interior({b}) = {}`
and `closure({b}) = {b,c}`. For measure, use the partition
`{a,b}` / `{c,d}` with masses `1/3` and `2/3`; the checker verifies
normalization, finite additivity, and the event/complement identity.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-measure-v0
```

## Horizon

Dedicated `finite-sets-v0` and `relations-functions-v0` packs are still needed.
ZFC, ordinals, choice, infinite cardinality, arbitrary topological spaces, and
countable additivity remain proof-horizon material.
