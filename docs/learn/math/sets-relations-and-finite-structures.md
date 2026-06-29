# Sets, Relations, And Finite Structures

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`,
  `curriculum_cardinality`, and `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `field_topology` and `field_measure_theory` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)

Example packs:

- [finite-sets-v0](../../../artifacts/examples/math/finite-sets-v0/)
- [relations-functions-v0](../../../artifacts/examples/math/relations-functions-v0/)
- [finite-cardinality-v0](../../../artifacts/examples/math/finite-cardinality-v0/)
- [finite-topology-v0](../../../artifacts/examples/math/finite-topology-v0/)
- [finite-measure-v0](../../../artifacts/examples/math/finite-measure-v0/)

## What Axeyum Checks

The current finite-structure path starts with plain finite sets, then moves to
relations, functions, cardinality, and set families. The finite-set pack replays
union/intersection identities, subset transitivity, and a fixed false set claim.
The relations/functions pack checks partial-order properties, bijective function
tables, and rejection of a multi-valued graph. The finite-cardinality pack
checks explicit bijections, proper-subset injections, finite injection and
surjection refutations, and an infinite-cardinality Lean-horizon row. The
topology pack checks empty/universe membership, closure under finite unions and
intersections, closure/interior computation, and finite metric balls. The
measure pack checks finite sigma-algebra closure, rational measure tables,
finite additivity, and event/complement identities.

## Encode / Check Walkthrough

For sets, encode membership over one finite universe:

```text
U = {a,b,c,d}
A = {a,b}
B = {b,c}
C = {c,d}
```

The validator recomputes `A union (B intersect C)` and
`(A union B) intersect (A union C)` directly. For relations and functions, encode
ordered pairs:

```text
domain = {x0,x1,x2}
codomain = {y0,y1,y2}
graph = {(x0,y1), (x1,y2), (x2,y0)}
```

The validator checks totality, single-valuedness, injectivity, and
surjectivity. For finite cardinality, encode the same function graph as a
cardinality witness:

```text
domain = {a,b,c}
codomain = {0,1,2}
bijection = {(a,1), (b,2), (c,0)}
```

The cardinality validator checks that the graph is total, single-valued,
injective, and surjective. It also enumerates fixed function spaces to reject an
injection `4 -> 3` and a surjection `2 -> 3`, while keeping Cantor diagonal as a
Lean-horizon theorem target.

For topology, the same finite-set discipline scales up to set families:

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
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-sets-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/relations-functions-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cardinality-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-measure-v0
```

For a fuller trace through finite topology and measure replay, read
[End To End: Finite Topology And Measure](finite-structures-end-to-end.md).

## Horizon

The finite set, relation/function, and cardinality packs are now checked finite
artifacts. The next finite-structure gaps are stronger EUF/Alethe evidence for
congruence examples and Lean artifacts for infinite theorems. ZFC, ordinals,
choice, infinite cardinality, arbitrary topological spaces, and countable
additivity remain proof-horizon material.
