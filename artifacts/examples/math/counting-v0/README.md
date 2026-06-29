# Counting V0

This pack covers the first core curriculum slice for counting and finite
combinatorics: permutations, combinations, Pascal's identity, and a tiny
pigeonhole impossibility.

The examples are finite arithmetic/enumeration artifacts:

- check a fixed permutation count `P(5, 3) = 60`;
- check Pascal's identity at `n = 6`, `k = 3`;
- exhaustively reject an injection from three pigeons into two holes.

These rows are fixed finite checks, not general combinatorics. They establish
the data shape for future SAT/CNF encoders, cardinality packs, recurrence
examples, and proof-certificate upgrades.

## Concepts

- `curriculum_counting`
- `field_discrete_math`
- `field_probability_theory`

## Trust Story

The validator computes factorial, permutation, and combination counts using
integer arithmetic. For the pigeonhole row, it enumerates every function from
the pigeon set to the hole set and confirms none is injective.

The current pigeonhole evidence is a checked finite enumeration, not a CNF/LRAT
proof object. The Boolean CNF recipe remains the graduation route for a
certificate-producing SAT proof.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/counting-v0
```
