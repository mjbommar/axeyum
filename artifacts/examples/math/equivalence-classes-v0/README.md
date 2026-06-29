# Equivalence Classes V0

This pack deepens the `relations-and-functions` curriculum node with finite
equivalence relations, partitions, and quotient maps. It sits after
`relations-functions-v0`: that pack checks generic relation and function table
properties, while this pack checks the specific table discipline behind
equivalence classes.

The examples are:

- a same-parity equivalence relation on `{0, 1, 2, 3}`;
- a quotient map whose fibers are exactly the equivalence classes;
- a partition-to-relation round trip;
- checked rejection of a symmetric, reflexive, but non-transitive relation;
- a QF_UF/Alethe quotient-map congruence conflict.

## Concepts

- `curriculum_relations_and_functions`
- `curriculum_sets`
- `curriculum_cardinality`
- `field_set_theory_and_foundations`
- `field_discrete_math`

## Trust Story

The validator recomputes relation properties and classes from finite tables. It
checks that listed blocks form a partition, that induced relations match the
listed pair set, that quotient maps are total and single-valued, and that
quotient-map fibers agree with the equivalence classes.

This is finite checked evidence plus one proof-object row. The proof-object row
uses the SMT-LIB artifact in `smt2/quotient-map-congruence-conflict.smt2` and a
solver regression requiring zero-trust `Evidence::UnsatAletheProof`. It does not
prove quotient constructions over arbitrary sets, choice principles, or infinite
cardinality facts.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/equivalence-classes-v0
```
