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
- [function-composition-v0](../../../artifacts/examples/math/function-composition-v0/)
- [finite-monoids-v0](../../../artifacts/examples/math/finite-monoids-v0/)
- [finite-permutation-groups-v0](../../../artifacts/examples/math/finite-permutation-groups-v0/)
- [finite-group-actions-v0](../../../artifacts/examples/math/finite-group-actions-v0/)
- [finite-order-lattices-v0](../../../artifacts/examples/math/finite-order-lattices-v0/)
- [finite-cardinality-v0](../../../artifacts/examples/math/finite-cardinality-v0/)
- [cardinality-principles-v0](../../../artifacts/examples/math/cardinality-principles-v0/)
- [finite-topology-v0](../../../artifacts/examples/math/finite-topology-v0/)
- [finite-quotient-topology-v0](../../../artifacts/examples/math/finite-quotient-topology-v0/)
- [finite-specialization-order-v0](../../../artifacts/examples/math/finite-specialization-order-v0/)
- [finite-compactness-v0](../../../artifacts/examples/math/finite-compactness-v0/)
- [finite-connectedness-v0](../../../artifacts/examples/math/finite-connectedness-v0/)
- [finite-continuous-maps-v0](../../../artifacts/examples/math/finite-continuous-maps-v0/)
- [finite-simplicial-homology-v0](../../../artifacts/examples/math/finite-simplicial-homology-v0/)
- [finite-chain-complex-torsion-v0](../../../artifacts/examples/math/finite-chain-complex-torsion-v0/)
- [finite-simplicial-cohomology-v0](../../../artifacts/examples/math/finite-simplicial-cohomology-v0/)
- [finite-universal-coefficient-shadow-v0](../../../artifacts/examples/math/finite-universal-coefficient-shadow-v0/)
- [finite-simplicial-cup-products-v0](../../../artifacts/examples/math/finite-simplicial-cup-products-v0/)
- [finite-measure-v0](../../../artifacts/examples/math/finite-measure-v0/)

## What Axeyum Checks

The current finite-structure path starts with plain finite sets, then moves to
relations, functions, cardinality, and set families. The finite-set pack replays
union/intersection identities, subset transitivity, and a fixed false set claim.
The relations/functions pack checks partial-order properties, bijective function
tables, rejection of a multi-valued graph, and a QF_UF/Alethe function
single-valuedness row. The equivalence-classes pack checks finite equivalence
classes, quotient-map fibers, partition-to-relation
round trips, rejection of a non-transitive relation, and a checked QF_UF/Alethe
quotient congruence row. The function-composition pack checks finite composition,
image/preimage replay, inverse tables, associativity, and non-injective inverse
counterexamples, plus a QF_UF/Alethe composition-application row. The
finite-monoids pack checks when a closed set of finite
functions forms a monoid under composition, including units and idempotents.
The finite-permutation-groups pack narrows finite endofunctions to bijections,
checks `S3` under composition, recomputes cycle/sign data, and replays the
natural action on the underlying set, with checked QF_UF/Alethe evidence for
the bad nonbijection row.
The finite-group-actions pack treats each group element as a
total function on a finite set, then checks action laws, orbit/stabilizer
replay, and Burnside fixed-point counting. The finite-order-lattices pack
checks finite partial orders, Boolean-lattice meet/join tables, distributivity,
monotone maps, fixed points, and a QF_UF/Alethe bad-order counterexample. The
finite-cardinality pack checks explicit bijections, proper-subset injections,
finite injection and surjection refutations, and an infinite-cardinality
Lean-horizon row. The cardinality-principles pack checks inclusion-exclusion,
disjoint-union additivity, double counting, powerset cardinality, invalid
additivity counterexamples, and a checked QF_LIA/Diophantine overlap-additivity
count contradiction. The
topology pack checks empty/universe membership, closure under finite unions and
intersections, closure/interior computation, and finite metric balls. The
finite-quotient-topology pack checks quotient-map fibers, same-fiber
equivalence pairs, quotient topology by preimage-open enumeration,
saturated-open image replay, and checked QF_UF/Alethe bad representative and
bad quotient-open rows.
The
finite-specialization-order pack derives a preorder from open neighborhoods,
checks singleton-closure characterization, confirms one finite `T0` slice, and
uses checked QF_UF/Alethe evidence for a false `T0`/antisymmetry claim. The
compactness pack checks finite open covers, subcovers, minimal-subcover
enumeration, finite-intersection families, and rejection of a bad cover. The
connectedness pack checks finite clopen-subset enumeration, open separations,
and rejection of a false connectedness claim. The continuous-map pack checks
finite function preimages of open sets, homeomorphism witnesses, and rejection
of false continuity/homeomorphism claims. The finite simplicial-homology pack
checks face closure for finite complexes, oriented-boundary replay,
`boundary^2 = 0`, and a fixed Betti-rank calculation. The finite
chain-complex-torsion pack checks a two-term integer complex, one-entry Smith
diagonal replay, a `Z/2` torsion generator, and a checked
QF_LIA/Diophantine bad-generator row. The measure pack checks finite
sigma-algebra closure, rational measure tables, finite additivity, and
event/complement identities.
The finite simplicial-cohomology pack checks F2 cochain coboundary replay,
`delta^2 = 0`, cohomology-rank replay for the same three-edge circle, and a
checked QF_UF/Alethe bad coboundary-value row.
The finite universal-coefficient shadow pack dualizes the integer `d1=[2]`
complex, checks `H^1 = Z/2`, replays the fixed degree-one Hom/Ext row, and
rejects `H^1 = 0` with checked QF_UF/Alethe evidence.
The finite simplicial-cup-products pack checks ordered-simplex F2 cup-product
replay, one finite coboundary-Leibniz row, and a checked QF_BV/DRAT bad
cup-product value row.

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
For function composition, encode total function tables:

```text
f(a0)=b0, f(a1)=b1, f(a2)=b0
g(b0)=c2, g(b1)=c0
(g o f)(a0)=c2, (g o f)(a1)=c0, (g o f)(a2)=c2
```

The validator recomputes composition, image/preimage sets, inverse tables for
bijections, associativity of three concrete functions, and a collision witness
showing that a non-injective function has no two-sided inverse.
For finite monoids, close a set of endofunctions under composition:

```text
id   : 0 -> 0, 1 -> 1
flip : 0 -> 1, 1 -> 0
zero : 0 -> 0, 1 -> 0
one  : 0 -> 1, 1 -> 1
```

The `finite-monoids-v0` validator recomputes the operation table as
composition, checks identity and associativity, finds the invertible elements
`id` and `flip`, and recomputes the idempotents `id`, `zero`, and `one`.

For finite permutation groups, restrict the function tables to bijections:

```text
points = 1, 2, 3
r(1)=2, r(2)=3, r(3)=1
s23(1)=1, s23(2)=3, s23(3)=2
r after s23 = s12
cycle_lengths(r) = [3]
sign(s23) = odd
```

The `finite-permutation-groups-v0` validator checks each map is bijective,
recomputes the `S3` composition table, recomputes cycle lengths and parity
signs, checks the sign homomorphism, and replays the natural action's orbit and
stabilizer for point `1`. The bad nonbijection row links the duplicate-image
conflict to checked QF_UF/Alethe evidence.

For a finite group action, the same total-function representation is indexed
by group elements:

```text
e(x) = x for every point x
s(01) = 10
s(10) = 01
s(00) = 00
s(11) = 11
```

The `finite-group-actions-v0` validator checks that `e` acts as the identity,
that `(g*h).x = g.(h.x)` for the listed group table, and that the resulting
function tables produce the claimed orbits and stabilizers. It also has
checked QF_UF/Alethe rows for malformed identity-action and compatibility
tables.

For finite order theory, encode the four-element Boolean lattice:

```text
elements = 0, A, B, AB
0 <= A, 0 <= B, A <= AB, B <= AB
A meet B = 0
A join B = AB
f(x) = x join A
fixed_points(f) = A, AB
```

The `finite-order-lattices-v0` validator checks the partial-order laws,
recomputes meet and join as greatest lower and least upper bounds, checks both
distributive laws over all triples, checks monotonicity of `f`, recomputes the
fixed points, links the bad antisymmetry row to checked QF_UF/Alethe evidence,
and links the false claim that `A` is top to a checked one-variable
Bool/CNF/LRAT refutation.
For finite quotient topology, reuse the quotient-map and finite-open-set data:

```text
X = {a,b,c}
open(X) = {}, {a,b}, {a,b,c}
q(a)=p, q(b)=p, q(c)=r
```

The `finite-quotient-topology-v0` validator recomputes fibers, the same-fiber
equivalence relation, every quotient subset preimage, and the saturated-open
image `{a,b} -> {p}`. It rejects the false claim that two representatives in
the same fiber have distinct quotient images, and it rejects the false claim
that `{r}` is quotient-open because its preimage `{c}` is not open in `X`.
Both fixed conflicts link to checked QF_UF/Alethe evidence.
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
For cardinality principles, encode concrete set and incidence tables:

```text
A = {a,b,c}
B = {b,c,d}
A union B = {a,b,c,d}
A intersect B = {b,c}
```

The validator checks inclusion-exclusion exactly. It also verifies disjoint
unions, bipartite edge double-counting, finite powersets, and an overlapping
counterexample to the false rule `|A union B| = |A| + |B|`. The promoted
solver row turns the replayed counts `4` and `6` into a source-linked
QF_LIA/Diophantine contradiction.

For topology, the same finite-set discipline scales up to set families:

```text
universe = a,b,c
open_sets = {}, {a}, {a,b}, {a,b,c}
subset = {b}
```

The validator checks the topology axioms and recomputes `interior({b}) = {}`
and `closure({b}) = {b,c}`. The finite specialization-order pack reuses the
same topology data and derives the specialization preorder:

```text
x <= y iff every open containing x also contains y
c <= b <= a
```

For the indiscrete two-point topology, the specialization preorder has both
`x <= y` and `y <= x`; the false `T0` row routes the resulting equality
conflict through checked QF_UF/Alethe evidence.

For compactness, the checker reuses finite topology data and recomputes
open-cover unions:

```text
universe = a,b,c
cover = {a,b}, {b,c}, {a,c}
subcover = {a,b}, {b,c}
```

It checks that the listed subcover covers the universe, enumerates smaller
subfamilies for the minimality row, and rejects the bad cover `{a}, {b}` because
it misses `c`; the final missing-point contradiction now has checked
Bool/CNF DRAT/LRAT evidence. For connectedness, enumerate all clopen subsets of a tiny
topology:

```text
universe = 0,1
open_sets = {}, {1}, {0,1}
clopen_subsets = {}, {0,1}
```

The checker confirms the Sierpinski example has no non-trivial clopen subset
and rejects the false claim that the discrete two-point topology is connected.
The base finite-topology pack also rejects a malformed open-set table that
omits the empty set; the final one-variable contradiction is checked through
the Boolean CNF DRAT/LRAT route.
For continuous maps, add a total map between finite topologies:

```text
open_X = {}, {1}, {0,1}
open_Y = {}, {v}, {u,v}
f(0) = u
f(1) = v
```

The checker recomputes every open-set preimage and rejects continuity when a
codomain-open set has a non-open preimage. For finite simplicial complexes,
the checker applies the same subset discipline to faces:

```text
simplices = [a], [b], [c], [a,b], [a,c], [b,c], [a,b,c]
boundary([a,b,c]) = [b,c] - [a,c] + [a,b]
```

It verifies face closure, recomputes the alternating boundary, and rejects the
false all-positive boundary.

For finite integer torsion, use a two-term free abelian chain complex:

```text
C1 = Z<e>
C0 = Z<v>
d1(e) = 2v
H0 = Z/2
```

The checker verifies `d0*d1 = 0`, replays the Smith diagonal `[2]`, checks that
`2v` is a boundary, and rejects the false claim that `v` is a boundary through
checked QF_LIA/Diophantine evidence for `2*k = 1`.

For finite cohomology, use F2 cochains on the same three-edge circle:

```text
f(a) = 0
f(b) = 1
f(c) = 0
delta f([a,c]) = 0
```

The checker recomputes coboundaries, `delta^2 = 0`, and the finite
cohomology dimensions `h0 = 1`, `h1 = 1`, then rejects a bad claim that
`delta f([a,c]) = 1` with checked QF_UF/Alethe evidence.
For finite cup products, keep the ordered filled triangle and split the
2-simplex:

```text
alpha([a,b]) = 1
beta([b,c]) = 1
(alpha cup beta)([a,b,c]) = 1
```

The checker recomputes the Alexander-Whitney split, checks one finite
`delta(f cup g) = delta(f) cup g + f cup delta(g)` row over `F2`, and rejects a
bad claim that `(alpha cup beta)([a,b,c]) = 0` with checked QF_BV/DRAT
evidence.
For measure, use the partition
`{a,b}` / `{c,d}` with masses `1/3` and `2/3`; the checker verifies
normalization, finite additivity, and the event/complement identity.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-sets-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/relations-functions-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/equivalence-classes-v0
cargo test -p axeyum-solver --test math_resource_uf_routes equivalence_classes_quotient_map_congruence_emits_checked_alethe
cargo test -p axeyum-solver --test math_resource_uf_routes qf_uf_resource_route_rejects_tampered_alethe_certificate
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/function-composition-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-monoids-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-permutation-groups-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-group-actions-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-order-lattices-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cardinality-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/cardinality-principles-v0
cargo test -p axeyum-solver --test math_resource_lia_routes cardinality_principles_overlap_additivity_emits_checked_diophantine_evidence
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes finite_topology_bad_empty_open_emits_checked_drat_and_lrat
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-quotient-topology-v0
cargo test -p axeyum-solver --test math_resource_uf_routes finite_quotient_topology_bad_open_emits_checked_alethe
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-specialization-order-v0
cargo test -p axeyum-solver --test math_resource_uf_routes finite_specialization_order_bad_t0_antisymmetry_emits_checked_alethe
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-compactness-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-connectedness-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes finite_connectedness_bad_connected_claim_emits_checked_drat_and_lrat
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-continuous-maps-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-homology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chain-complex-torsion-v0
cargo test -p axeyum-solver --test math_resource_lia_routes finite_chain_complex_torsion_bad_generator_emits_checked_diophantine_evidence
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-universal-coefficient-shadow-v0
cargo test -p axeyum-solver --test math_resource_uf_routes finite_universal_coefficient_bad_h1_zero_emits_checked_alethe
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-cohomology-v0
cargo test -p axeyum-solver --test math_resource_uf_routes finite_simplicial_cohomology_bad_coboundary_value_emits_checked_alethe
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-cup-products-v0
cargo test -p axeyum-solver --test math_resource_bv_routes finite_simplicial_cup_product_bad_value_emits_checked_bv_drat
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-measure-v0
```

For fuller traces through finite sets, relations/functions, equivalence
classes, function composition, finite function-table actions, finite
order/lattice replay, finite cardinality principles, topology, connectedness,
and measure replay, read
[End To End: Finite Sets](finite-sets-end-to-end.md),
[End To End: Relations And Functions](relations-functions-end-to-end.md),
[End To End: Equivalence Classes](equivalence-classes-end-to-end.md),
[End To End: Alethe Certificate Anatomy](alethe-certificate-anatomy-end-to-end.md),
[End To End: Function Composition](function-composition-end-to-end.md),
[End To End: Finite Monoids](finite-monoids-end-to-end.md),
[End To End: Finite Permutation Groups](finite-permutation-groups-end-to-end.md),
[End To End: Finite Group Actions And Burnside Counting](finite-group-actions-end-to-end.md),
[End To End: Finite Order Lattices](finite-order-lattices-end-to-end.md),
[End To End: Finite Cardinality](finite-cardinality-end-to-end.md),
[End To End: Cardinality Principles](cardinality-principles-end-to-end.md),
[End To End: Finite Algebra Homomorphisms](finite-algebra-homomorphisms-end-to-end.md),
[End To End: Finite Quotient Topology](finite-quotient-topology-end-to-end.md),
[End To End: Finite Specialization Order](finite-specialization-order-end-to-end.md),
[End To End: Finite Compactness](finite-compactness-end-to-end.md),
[End To End: Finite Connectedness](finite-connectedness-end-to-end.md),
[End To End: Finite Continuous Maps](finite-continuous-maps-end-to-end.md),
[End To End: Finite Simplicial Homology](finite-simplicial-homology-end-to-end.md),
[End To End: Finite Chain-Complex Torsion](finite-chain-complex-torsion-end-to-end.md),
[End To End: Finite Universal Coefficient Shadow](finite-universal-coefficient-shadow-end-to-end.md),
[End To End: Finite Simplicial Cohomology](finite-simplicial-cohomology-end-to-end.md),
[End To End: Finite Simplicial Cup Products](finite-simplicial-cup-products-end-to-end.md),
[End To End: Finite Topology, Connectedness, And Measure](finite-structures-end-to-end.md),
and [End To End: Finite Topology And Measure](finite-topology-measure-end-to-end.md).

## Horizon

The finite set, relation/function, equivalence-class, function-composition,
finite monoid, finite permutation-group, finite group-action, finite-order/lattice, cardinality,
cardinality-principles, topology, specialization-order, compactness-shadow, connectedness-shadow, continuous-map,
finite-simplicial-homology, finite-chain-complex-torsion, finite-universal-coefficient-shadow, finite-simplicial-cohomology, and measure packs are now checked finite artifacts.
The finite-simplicial-cup-products pack adds a checked finite cochain-operation
row without promoting general cohomology-ring laws.
The finite-simplicial-homology and finite-chain-complex-torsion packs now also
carry checked QF_LIA/Diophantine certificates for bad integer boundary
coefficients, boundary-square cancellation, and bad torsion-generator
membership. The
finite-universal-coefficient-shadow pack adds checked QF_UF/Alethe evidence
for a bad `H^1 = 0` group-identification row without promoting the general
theorem. The Alethe
certificate-anatomy page now shows the shared QF_UF proof-object boundary for
quotient-map congruence and tamper rejection. The next finite-structure gaps
are narrower EUF/Alethe anatomy for secondary algebra/topology packs and Lean
artifacts for infinite theorems. ZFC, ordinals, choice,
infinite cardinality, general monoid, permutation-group, and group-action theorems,
complete-lattice fixed-point theorems, arbitrary
topological spaces, general compactness, general connectedness,
continuous-image/homeomorphism theorems, homology invariance, exact sequences,
universal coefficient theorems, and countable additivity remain proof-horizon
material.
