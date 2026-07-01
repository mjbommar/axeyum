# Number Theory V0

This pack covers the first bounded destination slice for `number-theory`: CRT
compatibility, quadratic residues, sum-of-two-squares checks, and a fixed
linear Diophantine witness.

The examples are exact finite arithmetic artifacts:

- replay a compatible non-coprime CRT witness for `x = 8`;
- replay `4^2 = 5 mod 11`;
- reject `x^2 = 3 mod 7` by finite enumeration;
- refute the same modulo-7 nonresidue row as a QF_BV bit-blast conflict with
  checked DRAT evidence;
- reject the malformed square-root witness `2^2 = 2 mod 7`;
- refute that bad witness as a QF_BV bit-blast conflict with checked DRAT
  evidence;
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

The modulo-7 nonresidue row also has a QF_BV proof-route artifact:
[`smt2/quadratic-nonresidue-mod7-bitblast-conflict.smt2`](smt2/quadratic-nonresidue-mod7-bitblast-conflict.smt2).
It represents a candidate residue as a 3-bit word with `x < 7`, computes `x*x`
exactly after zero-extension, and refutes `x^2 mod 7 = 3` with a DIMACS/DRAT
certificate that `UnsatProof::recheck` validates. The modular lowering and
bit-blast/Tseitin steps remain explicit trust steps until Lean reconstruction
covers the original formula.

The bad square-root witness has the same proof-route shape in
[`smt2/bad-square-witness-mod7-bitblast-conflict.smt2`](smt2/bad-square-witness-mod7-bitblast-conflict.smt2):
the artifact computes `2*2 mod 7 = 4` at fixed width and refutes the malformed
target `2`.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/number-theory-v0
cargo test -p axeyum-solver --test math_resource_bv_routes number_theory_quadratic_nonresidue_emits_checked_bv_drat
cargo test -p axeyum-solver --test math_resource_bv_routes number_theory_bad_square_witness_emits_checked_bv_drat
```
