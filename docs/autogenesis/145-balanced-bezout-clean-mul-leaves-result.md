# Two clean target-owned multiplication leaves

Date: 2026-08-21

Primitive-induction replacements for multiplication associativity and right
distributivity compiled once, exported once, and reconstructed twice each.
Both batch audits are byte-identical; all four measured footprints are empty.

The replacement identities are:

- `balancedBezoutMulAssocLeafV1`:
  `3e1ef3dc51f2702b9b457e5621457542c07757b30a57cede7db9e5b7273f7c00`
- `balancedBezoutRightDistribLeafV1`:
  `7d41f955bf36b0825b925ec0d1d31b0df7551c0b413b0ed6cca4fcef1d833f05`

Neither depends on official `Nat.mul_assoc` or official `Nat.right_distrib`.
The first uses clean left distributivity and pointwise equality transport. The
second uses a clean private four-term addition permutation and transport.

The sealed pack is
`/nas3/data/axeyum/autogenesis/reference-packs/616fe5d01-balanced-bezout-clean-mul-leaves-v1`
with manifest SHA-256
`434b9490f1b317d037f5b9cad0799e09620b320650cdede4c34f02a045d1d61b`.
Exact cleanup restored the three-file `s5` baseline.

These two results close the leaf gap but do not yet close the update. The next
gate is a transparent wrapper applying the accepted parameterized V2 update to
these exact theorems, reconstructed independently twice.

```sh
python3 scripts/check-autogenesis-balanced-bezout-clean-mul-leaves-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_balanced_bezout_clean_mul_leaves_result
```
