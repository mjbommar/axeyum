# Finite Order Lattices V0

This pack extends the finite relations path with exact finite order and lattice
checks. It uses the four-element Boolean lattice `P({a,b})` as explicit
relation data, then checks meet/join tables, distributivity, a monotone map,
and its fixed points.

The pack covers:

- finite partial-order replay for a subset relation;
- bottom/top replay;
- meet and join table replay as greatest lower and least upper bounds;
- distributive lattice identity replay;
- monotone finite map and fixed-point replay;
- checked rejection of a non-partial-order relation by finite replay;
- a separate checked QF_UF/Alethe proof row for the bad antisymmetry equality;
- checked Bool/CNF DRAT/LRAT rejection of a false top-element claim;
- a Lean-horizon row for general order and lattice theory.

## Concepts

- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_cardinality`
- `field_set_theory_and_foundations`
- `field_discrete_math`
- `field_logic_and_proof`

## Trust Story

The validator parses finite carrier elements, relation pairs, operation tables,
and finite maps. It checks partial-order laws by enumeration, recomputes
greatest lower bounds and least upper bounds, checks distributivity over all
triples, checks monotonicity over all comparable pairs, and recomputes fixed
points.

For the bad partial-order row, exact relation replay identifies `x <= y` and
`y <= x` for distinct elements. The separate
`qf-uf-bad-partial-order-antisymmetry` row links the `QF_UF` artifact that fixes
the antisymmetry consequence `x = y`, refutes it against `x != y`, and checks
the resulting `UnsatAletheProof` independently.

For the bad top-element row, exact relation replay identifies that `B <= A` is
false in the Boolean lattice, while the false claim that `A` is top requires
`B <= A`. The linked DIMACS artifact isolates that one-variable contradiction
and the resource regression checks both DRAT and LRAT proof objects.

This is a finite replay pack. It does not prove complete-lattice fixed-point
theorems, domain theory, Galois connections, Boolean representation theorems,
or infinite order-theoretic facts.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-order-lattices-v0
```
