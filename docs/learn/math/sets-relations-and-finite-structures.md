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
- [equivalence-classes-v0](../../../artifacts/examples/math/equivalence-classes-v0/)
- [finite-cardinality-v0](../../../artifacts/examples/math/finite-cardinality-v0/)
- [finite-topology-v0](../../../artifacts/examples/math/finite-topology-v0/)
- [finite-compactness-v0](../../../artifacts/examples/math/finite-compactness-v0/)
- [finite-connectedness-v0](../../../artifacts/examples/math/finite-connectedness-v0/)
- [finite-continuous-maps-v0](../../../artifacts/examples/math/finite-continuous-maps-v0/)
- [finite-measure-v0](../../../artifacts/examples/math/finite-measure-v0/)

## What Axeyum Checks

The current finite-structure path starts with plain finite sets, then moves to
relations, functions, cardinality, and set families. The finite-set pack replays
union/intersection identities, subset transitivity, and a fixed false set claim.
The relations/functions pack checks partial-order properties, bijective function
tables, and rejection of a multi-valued graph. The equivalence-classes pack
checks finite equivalence classes, quotient-map fibers, partition-to-relation
round trips, rejection of a non-transitive relation, and an explicit QF_UF/Alethe
proof gap. The finite-cardinality pack checks explicit bijections,
proper-subset injections, finite injection and surjection refutations, and an
infinite-cardinality Lean-horizon row. The
topology pack checks empty/universe membership, closure under finite unions and
intersections, closure/interior computation, and finite metric balls. The
compactness pack checks finite open covers, subcovers, minimal-subcover
enumeration, finite-intersection families, and rejection of a bad cover. The
connectedness pack checks finite clopen-subset enumeration, open separations,
and rejection of a false connectedness claim. The continuous-map pack checks
finite function preimages of open sets, homeomorphism witnesses, and rejection
of false continuity/homeomorphism claims. The measure pack checks finite
sigma-algebra closure, rational measure tables, finite additivity, and
event/complement identities.

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
surjectivity. For equivalence classes, encode relation pairs and the quotient
map:

```text
elements = {0,1,2,3}
classes = even:{0,2}, odd:{1,3}
q(0)=even, q(1)=odd, q(2)=even, q(3)=odd
```

The checker recomputes reflexivity, symmetry, transitivity, class fibers, and
the equivalence:

```text
x ~ y iff q(x) = q(y)
```

It rejects a relation with `a ~ b` and `b ~ c` but missing `a ~ c`.
For finite cardinality, encode the same function graph as a cardinality witness:

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
and `closure({b}) = {b,c}`. For compactness, the checker reuses finite
topology data and recomputes open-cover unions:

```text
universe = a,b,c
cover = {a,b}, {b,c}, {a,c}
subcover = {a,b}, {b,c}
```

It checks that the listed subcover covers the universe, enumerates smaller
subfamilies for the minimality row, and rejects the bad cover `{a}, {b}` because
it misses `c`. For connectedness, enumerate all clopen subsets of a tiny
topology:

```text
universe = 0,1
open_sets = {}, {1}, {0,1}
clopen_subsets = {}, {0,1}
```

The checker confirms the Sierpinski example has no non-trivial clopen subset
and rejects the false claim that the discrete two-point topology is connected.
For continuous maps, add a total map between finite topologies:

```text
open_X = {}, {1}, {0,1}
open_Y = {}, {v}, {u,v}
f(0) = u
f(1) = v
```

The checker recomputes every open-set preimage and rejects continuity when a
codomain-open set has a non-open preimage. For measure, use the partition
`{a,b}` / `{c,d}` with masses `1/3` and `2/3`; the checker verifies
normalization, finite additivity, and the event/complement identity.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-sets-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/relations-functions-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/equivalence-classes-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cardinality-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-compactness-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-connectedness-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-continuous-maps-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-measure-v0
```

For a fuller trace through finite topology, connectedness, and measure replay,
read [End To End: Finite Topology, Connectedness, And Measure](finite-structures-end-to-end.md).

## Horizon

The finite set, relation/function, equivalence-class, cardinality, topology,
compactness-shadow, connectedness-shadow, continuous-map, and measure packs are
now checked finite artifacts. The next finite-structure gaps are stronger
EUF/Alethe evidence for congruence examples and Lean artifacts for infinite
theorems. ZFC, ordinals, choice, infinite cardinality, arbitrary topological
spaces, general compactness, general connectedness,
continuous-image/homeomorphism theorems, and countable additivity remain
proof-horizon material.
