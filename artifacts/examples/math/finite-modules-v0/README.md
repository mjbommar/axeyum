# Finite Modules V0

This pack extends the finite algebra and linear-algebra bridge with exact
finite module checks over `Z/4Z`. It treats the regular module `Z/4Z` as a
finite ring action on a finite additive group, then checks submodules,
generated submodules, module homomorphisms, kernels, images, and quotient
module tables.

The pack covers:

- finite left-module table replay for `Z/4Z` acting on itself;
- submodule and generated-submodule replay for `{0, 2}`;
- module-homomorphism replay for multiplication by `2`;
- kernel/image replay for the endomorphism;
- quotient-module addition and scalar-action table replay;
- checked rejection of a non-submodule by exact replay;
- an explicit QF_UF/Alethe scalar-closure contradiction row;
- a Lean-horizon row for general module theory and homological algebra.

## Concepts

- `curriculum_rings`
- `curriculum_groups`
- `curriculum_linear_algebra`
- `field_abstract_algebra`
- `field_linear_algebra`
- `field_set_theory_and_foundations`

## Trust Story

The validator parses finite ring tables, module addition tables, scalar
multiplication tables, finite subsets, finite maps, and coset tables. It checks
the module laws by finite enumeration, recomputes the generated submodule,
checks additive and scalar preservation for the homomorphism, recomputes kernel
and image, and verifies quotient tables from representatives.

For the bad submodule rows, exact replay computes `2 * 1 = 2` in the regular
`Z/4Z` module while the claimed subset marks `1` present and `2` absent. The
separate `QF_UF` row refutes the fixed scalar-closure membership claim and
checks the resulting `UnsatAletheProof` independently.

This is a finite replay pack. It does not prove general module theorems,
Noetherian structure, tensor products, exactness, projective or injective
module facts, or homological algebra.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-modules-v0
```
