# Finite Permutation Groups V0

This pack covers the canonical bridge from finite functions to group theory:
permutations are bijective self-maps, and a finite permutation group is closed
under composition.

The examples are fixed finite artifacts:

- replay the symmetric group `S3` as six bijections on a three-point set;
- recompute the Cayley table from function composition;
- recompute cycle lengths and the parity/sign homomorphism;
- replay the natural action of `S3` on the three points, including
  orbit-stabilizer counts;
- reject a total self-map that is not bijective by finite replay;
- check the duplicate-preimage injectivity conflict with QF_UF/Alethe evidence.

These checks do not claim general permutation-group theory, Cayley's theorem,
Sylow theory, representation theory, or classification results.

## Concepts

- `curriculum_groups`
- `curriculum_relations_and_functions`
- `curriculum_counting`
- `field_abstract_algebra`
- `field_discrete_math`
- `field_set_theory_and_foundations`

## Trust Story

The validator checks the finite Cayley table, verifies every listed element is
a bijection, recomputes composition from the underlying maps, recomputes cycle
lengths and signs, checks sign preservation under multiplication, and replays
the natural action table. The rejected row is checked by confirming the claimed
self-map has a duplicated image and a missing image, so it cannot be a
permutation. The separate `qf-uf-bad-nonbijection-injectivity` row turns the
duplicate-image conflict into an independently checked `UnsatAletheProof`.

The current route is deterministic finite-model replay plus a small EUF
certificate for the explicit bad-nonbijection injectivity row. Graduation means lowering more
table/function constraints into Axeyum finite-domain or EUF terms and attaching
checked proof objects for universal/refutation rows.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-permutation-groups-v0
```
