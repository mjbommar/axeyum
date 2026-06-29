# Modular Arithmetic V0

This pack covers the first concrete number-theory item from the curriculum
backlog: congruences, modular inverses, CRT witnesses, and composite-modulus
counterexamples.

The pack is intentionally finite and exact. The validator checks the arithmetic
directly over small integers; solver encoding and proof-producing evidence are
graduation steps.

## Concepts

- `curriculum_modular_arithmetic`
- `curriculum_divisibility_and_euclid`
- `curriculum_fields`
- `field_number_theory`
- `field_abstract_algebra`

## Trust Story

- SAT-style examples are replayed by checking the documented witnesses.
- UNSAT-style examples are checked by exhaustive finite search over the stated
  modulus.
- No SMT proof certificate is claimed yet.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
```
