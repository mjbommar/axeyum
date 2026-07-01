# Finite Monoid Checks

This pack adds a finite bridge between functions and groups. It models the
full transformation monoid on a two-element set: all total functions
`{0,1} -> {0,1}` under composition.

It checks:

- finite monoid identity and associativity laws;
- composition-table replay from the underlying function tables;
- units and idempotents in the monoid;
- exact replay rejection of a malformed non-associative table;
- checked QF_UF/Alethe evidence for the malformed associativity equality;
- general monoid and semigroup theory as Lean horizon.

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-monoids-v0
```
