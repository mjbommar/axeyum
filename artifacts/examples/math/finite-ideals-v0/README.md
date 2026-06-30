# Finite Ideals V0

This pack extends the finite ring and module bridge with exact finite ideal and
quotient-ring checks over `Z/6Z`. It treats an ideal as finite additive
subgroup data plus left/right absorption under ring multiplication, then checks
a principal ideal, a quotient ring, and a ring-homomorphism kernel.

The pack covers:

- two-sided ideal replay for the even residues `{0, 2, 4}` in `Z/6Z`;
- principal-ideal generation from `2`;
- reduction modulo `2` as a unital ring homomorphism;
- kernel/image replay for that ring homomorphism;
- quotient-ring addition and multiplication table replay;
- checked quotient-ring representative congruence with QF_UF/Alethe evidence;
- checked rejection of a non-ideal subset with QF_UF/Alethe evidence;
- a Lean-horizon row for general ideal and quotient-ring theory.

## Concepts

- `curriculum_rings`
- `curriculum_modular_arithmetic`
- `field_abstract_algebra`
- `field_number_theory`
- `field_set_theory_and_foundations`

## Trust Story

The validator parses finite ring tables, candidate ideals, finite maps, and
coset tables. It checks ring axioms, ideal additive subgroup closure, left and
right absorption by every ring element, finite generated-ideal closure,
ring-homomorphism preservation, kernel/image recomputation, and quotient-ring
operations from representatives.

The quotient representative row links the well-definedness obligation to a
small QF_UF/Alethe proof: equal quotient classes must produce equal quotient
addition results, independent of representative choice.

For the bad ideal row, exact replay computes `2 + 2 = 4` in `Z/6Z` while the
claimed subset marks `2` present and `4` absent. The linked `QF_UF` artifact
refutes the fixed additive-closure membership claim and checks the resulting
`UnsatAletheProof` independently.

This is a finite replay pack. It does not prove ideal correspondence,
prime/maximal ideal theory, localization, Noetherianity, or algebraic geometry.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-ideals-v0
```
