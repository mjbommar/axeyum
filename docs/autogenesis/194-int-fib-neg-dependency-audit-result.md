# Exact `Int.fib_neg` dependency audit result

Date: 2026-08-21

## Result

One preregistered reread classified all 26 direct dependencies of official
`Int.fib_neg`: 14 have empty kernel footprints and 12 are `propext`-bearing.
The clean set includes equality transport, conditionals, sign arithmetic, and
the crucial integer case split `Int.eq_nat_or_neg`.

The central negative-natural-number theorem `Int.fib_neg_natCast` is not clean.
It carries the complete nine-name footprint seen at the root and has 36 direct
dependencies. Therefore the official theorem cannot be recovered merely by
reassembling its immediate children. The smallest honest next frontier is the
36-root surface beneath `Int.fib_neg_natCast`, not the already clean outer
integer case split.

No proof material was rendered and no theorem or ledger credit was granted.
The immutable classification pack is
`/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-dependency-audit-v1/`;
its manifest SHA-256 is
`8233a87e297d488fb94b0611b0127303b70fb62510463afd75b234cae81711af`.

## Verification

```sh
python3 scripts/check-autogenesis-int-fib-neg-dependency-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_int_fib_neg_dependency_audit_result
```
