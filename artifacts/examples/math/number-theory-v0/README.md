# Number Theory V0

This pack covers the first bounded destination slice for `number-theory`: CRT
compatibility, quadratic residues, sum-of-two-squares checks, and a fixed
linear Diophantine witness.

The examples are exact finite arithmetic artifacts:

- replay a compatible non-coprime CRT witness for `x = 8`;
- replay `4^2 = 5 mod 11`;
- reject `x^2 = 3 mod 7` by finite enumeration;
- replay `65 = 1^2 + 8^2`;
- reject `7 = a^2 + b^2` by the mod-4 square obstruction;
- replay `14*(-1) + 21*1 = 7`.

These checks do not claim the full Chinese remainder theorem, quadratic
reciprocity, the two-squares theorem, the fundamental theorem of arithmetic, or
infinitude of primes.

## Concepts

- `curriculum_number_theory`
- `curriculum_divisibility_and_euclid`
- `curriculum_modular_arithmetic`
- `field_number_theory`

## Trust Story

The validator recomputes every witness with exact integers. The negative rows
are accepted only after exhaustive residue enumeration or a fixed modular
obstruction. General number-theory theorems remain Lean-horizon; this pack is a
bounded compute-and-check surface.

This pack does not yet emit Axeyum BV/LIA terms or proof certificates. The
graduation route is to lower finite residue searches into BV/enumeration and
linear Diophantine rows into QF_LIA `UnsatDiophantine` evidence where
applicable.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/number-theory-v0
```
