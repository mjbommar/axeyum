# `Nat.gcd_fib_add_self` divisibility-antisymmetry audit result

Date: 2026-08-21

One nonrendering importer pass audited the five direct theorem dependencies of
official `Nat.dvd_antisymm`. Four are already empty-footprint:

- `Eq.symm`;
- `Nat.eq_zero_of_zero_dvd`;
- `Nat.le_antisymm`;
- `Nat.succ_pos`.

The sole `propext` carrier is `Nat.le_of_dvd`. Its direct dependency set reaches
the generated simplification theorem `Nat.lt_irrefl._simp_1`; the other four
dependencies do not carry assumptions.

This narrows the remaining gcd-extensionality work from replacing
`Nat.dvd_antisymm` wholesale to one explicit contract seam. The next increment
must preregister a target-owned antisymmetry theorem parameterized only over a
clean `le_of_dvd` implementation, while reusing the four measured clean leaves.

No theorem was submitted and no proof term, theorem type, or theorem value was
rendered. The sealed evidence pack is
`/nas3/data/axeyum/autogenesis/reference-packs/76462c935-gcd-shift-dvd-antisymm-dependency-audit-v1`
with manifest SHA-256
`78bfd1a6ff42c82db971c4bc6f91d7d54cfeff42c378404ea21d4ac7c1f8ec24`.

```sh
python3 scripts/check-autogenesis-nat-gcd-fib-add-self-dvd-antisymm-dependency-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_dvd_antisymm_dependency_audit_result
```
