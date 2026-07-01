# Modular Arithmetic V0

This pack covers the first concrete number-theory item from the curriculum
backlog: congruences, modular inverses, CRT witnesses, and composite-modulus
counterexamples.

The pack is intentionally finite and exact. The validator checks the arithmetic
directly over small integers. It also includes promoted solver-form
Diophantine obstructions for the composite non-unit inverse claim and an
incompatible non-coprime CRT claim, plus fixed-width QF_BV/DRAT proof routes
for the composite non-unit inverse search and the modulo-5 Fermat-unit
counterexample search.

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
- The `qf-lia-nonunit-diophantine` row encodes `2*b == 1 (mod 6)` as the
  integer equation `2*b - 6*k = 1`; Axeyum emits an `UnsatDiophantine`
  certificate and `Evidence::check` independently rechecks the gcd obstruction.
- The `composite-nonunit-no-inverse-qf-bv-drat` row encodes the same finite
  residue search as a 3-bit candidate `b < 6`; Axeyum bit-blasts the modular
  multiplication/remainder formula, emits DRAT evidence, and rechecks the
  DIMACS/DRAT pair independently.
- The `qf-lia-incompatible-crt-diophantine` row encodes the incompatible CRT
  pair `x == 1 mod 4`, `x == 2 mod 6` as `4*a - 6*b = 1`; the same checked
  certificate route records that `gcd(4,6)=2` does not divide `1`.
- The `fermat-units-mod-prime-qf-bv-drat` row encodes the finite search for
  a unit `a` modulo `5` with `a^4 != 1` as a 3-bit residue query. Axeyum
  bit-blasts the fixed-width formula, emits DRAT evidence, and rechecks the
  DIMACS/DRAT pair independently.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
cargo test -p axeyum-solver --test math_resource_lia_routes modular_incompatible_crt_emits_checked_diophantine_evidence
cargo test -p axeyum-solver --test math_resource_bv_routes modular_arithmetic_nonunit_inverse_mod6_emits_checked_bv_drat
cargo test -p axeyum-solver --test math_resource_bv_routes modular_arithmetic_fermat_units_mod5_emits_checked_bv_drat
```
