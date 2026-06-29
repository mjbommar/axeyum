# Finite Sets V0

This pack covers the first core curriculum slice for `sets`: finite universes,
membership as characteristic bits, subset checks, and union/intersection
identities. It is deliberately small and replay-oriented.

The examples are the set-theory shadow of Axeyum's Bool/BV route:

- replay a distributive finite-set identity over one explicit universe;
- replay subset transitivity over nested finite sets;
- reject a malformed fixed distributive claim by recomputing both sides.

These checks do not claim to prove ZFC set theory or general infinite-set
theorems. They establish a checked finite model pattern that later packs for
relations, functions, cardinality, topology, measure, and probability can reuse.

## Concepts

- `curriculum_sets`
- `field_set_theory_and_foundations`

## Trust Story

The current validator checks that every listed subset is contained in its finite
universe, then recomputes the claimed set operations directly. The `sat` rows
are accepted only when the replayed fixed witness satisfies the claim. The
`unsat` row is a bounded fixed-claim rejection: the checker recomputes both
sides of the malformed identity and confirms that equality fails on the listed
sets.

This pack does not yet emit Bool/BV terms, call Axeyum, produce CNF, or check
LRAT/DRAT certificates for universal set identities. Those routes are graduation
targets once finite-set encoders are reused by several packs.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-sets-v0
```
