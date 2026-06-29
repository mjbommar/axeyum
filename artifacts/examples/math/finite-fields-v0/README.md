# Finite Fields V0

This pack covers the first core curriculum slice for `fields`: prime moduli as
finite fields and composite moduli as non-field rings. It uses tiny fixed
moduli so every claim can be replayed or exhaustively checked.

The examples are the finite algebra shadow of Axeyum's BV/enumeration route:

- replay a complete nonzero inverse table for `F_7`;
- exhaustively reject a distributivity counterexample in `F_5`;
- exhaustively reject the claim that `2` has an inverse modulo `6`.

These checks are not a proof of general field theory. They are concrete finite
artifacts that teach why prime moduli are fields and composite moduli can fail
the field axioms.

## Concepts

- `curriculum_fields`
- `curriculum_modular_arithmetic`
- `curriculum_rings`
- `field_abstract_algebra`
- `field_number_theory`

## Trust Story

The validator checks moduli, residue ranges, inverse-table entries, and finite
universal claims by enumeration. The `F_7` inverse table is replay-only evidence:
the table is accepted because each row multiplies to `1 mod 7`. The
distributivity and composite no-inverse rows are checked finite rejections:
the validator enumerates the entire relevant residue space.

This pack does not yet emit Axeyum BV terms or proof certificates. The
graduation route is deterministic BV/CNF emission plus checked bit-blast
evidence for the fixed finite obligations.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-fields-v0
```
