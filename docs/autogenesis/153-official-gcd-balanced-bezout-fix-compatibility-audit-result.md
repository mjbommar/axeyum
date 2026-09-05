# `WellFounded.fix` compatibility-audit result

Date: 2026-08-21

Two complete proof-free audits are byte-identical. The mismatch is a genuine
representation boundary, not binder metadata:

- the generic source has a nine-name closure over the official inductive
  `WellFounded` package;
- the target support kernel has a five-name closure and represents
  `WellFounded` as a definition;
- `WellFounded.apply`, `WellFounded.fixF`, `WellFounded.intro`, and
<!-- absent: WellFounded.apply, WellFounded.fixF, WellFounded.intro, WellFounded.rec -->
  `WellFounded.rec` are absent from the target;
- four shared declarations are kernel-type-shape compatible, while
  `WellFounded.fix` alone has incompatible type shapes.

The audit rendered no proof, theorem type, definition value, or theorem value,
and attempted no composition or theorem submission. Its selected repair is to
reconstruct clean gcd computation leaves inside the official generic kernel,
where the complete source representation already exists. Importing the native
`WellFounded` representation, translating between the two, and retrying the
closed theorem remain unauthorized.

The sealed pack is
`/nas3/data/axeyum/autogenesis/reference-packs/7550b31c4-official-gcd-balanced-bezout-fix-audit-v1`
with manifest SHA-256
`b6cfa19fadc1651daca57bae21dad29d501cd8938b1bc493211b2eac6196d423`.

```sh
python3 scripts/check-autogenesis-official-gcd-balanced-bezout-fix-compatibility-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_fix_compatibility_audit_result
```
