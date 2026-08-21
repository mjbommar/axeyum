# Extended-gcd coefficient root audit result

Date: 2026-08-21

## Result

The preregistered single export and single importer pass completed exactly once.
Pinned Mathlib 4.30 theorem `Nat.gcd_eq_gcd_ab` is **not** an admissible bridge
as a whole. Axeyum independently reports this complete kernel footprint:

```text
Quot, Quot.lift, Quot.mk, Quot.sound, propext
```

The root is therefore reference evidence only. No coefficient adapter,
reconstruction, theorem credit, fact-status change, or ledger write occurred.

## Exact next frontier

The same pass exposes exactly twelve direct theorem dependencies:

```text
Eq.trans
Int.mul_zero
Nat.xgcdAux_val
Nat.xgcd_val
_private.Mathlib.Data.Int.GCD.0.Nat.xgcdAux_P
add_zero
congr
congrArg
eq_self
mul_one
of_eq_true
zero_add
```

The meaningful candidates are the two public xgcd value equations and the
private xgcd invariant; the remaining equality and arithmetic leaves are likely
foundation support, but that is not assumed. The next increment must
preregister a single reread of this already-sealed stream for all twelve roots.
Only that measurement can distinguish a clean coefficient core from a route
whose contamination is intrinsic.

## Durable evidence

The immutable reference pack is
`/nas3/data/axeyum/autogenesis/reference-packs/609241d91-extended-gcd-root-audit-v1/`.
Its manifest is mode `0444`, SHA-256
`f7a9ad05d609a2fe54da044d5c30c964a53b9432fccf6548ca254026c4a95ab8`;
the directory is mode `0555`. The raw 2,497,293-byte NDJSON remains restricted
to Axeyum's importer and was never printed or rendered into model context.

## Verification

```sh
python3 scripts/check-autogenesis-extended-gcd-root-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_extended_gcd_root_audit_result
```
