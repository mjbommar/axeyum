# `WellFounded.fix` compatibility-audit plan

Date: 2026-08-21

The closed balanced-Bézout specialization stopped at a structural mismatch in
`WellFounded.fix`. This audit will rebuild the exact source and target kernels
from the same four pinned streams, but it will not retry composition or submit
any theorem.

For `WellFounded.fix` and the union of its two named dependency closures, the
new diagnostic mode may emit only declaration names, kinds, content/type
hashes, compatibility classes, and counts. Proofs, theorem types, definition
values, and theorem values remain non-renderable. Two complete invocations must
produce byte-identical reports.

The audit must preserve the already observed root shapes `f45b2305…` and
`0c2e9552…`. It will distinguish exact, alpha-type, kernel-shape,
translated-definitional, missing, and genuinely mismatched rows. That evidence
will select one later repair; it grants no transport or reconstruction
authority itself.

```sh
python3 scripts/check-autogenesis-official-gcd-balanced-bezout-fix-compatibility-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_fix_compatibility_audit_plan
```
