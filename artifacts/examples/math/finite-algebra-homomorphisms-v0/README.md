# Finite Algebra Homomorphisms V0

This pack extends the finite algebra path from Cayley tables to
structure-preserving maps. It uses reduction modulo `2` from `Z/4Z` to `Z/2Z`
as a single exact example that supports group homomorphism, ring homomorphism,
kernel/image, and quotient replay.

The pack covers:

- group homomorphism replay for addition tables;
- kernel and image recomputation;
- a finite quotient and induced-isomorphism replay;
- unital ring homomorphism replay for addition and multiplication tables;
- checked rejection of a bad group-homomorphism table;
- a Lean-horizon row for general isomorphism theorems.

## Concepts

- `curriculum_groups`
- `curriculum_rings`
- `curriculum_relations_and_functions`
- `field_abstract_algebra`
- `field_set_theory_and_foundations`

## Trust Story

The validator parses finite operation tables and a total map between carriers.
It checks every source pair against the codomain operation, recomputes kernels
and images, verifies quotient cosets and quotient operations, and checks the
induced map by exact finite enumeration.

This is a finite replay pack. It does not prove the group or ring isomorphism
theorems in general, module theory, category-theoretic universal properties, or
infinite algebra.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-algebra-homomorphisms-v0
```
