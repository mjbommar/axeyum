# Subtractive gcd dependency audit result

Date: 2026-08-21

## Result

The one sealed-stream reread split the 14 previously unmeasured direct
dependencies exactly in half:

- Seven are empty-footprint: equality symmetry/transitivity, `Nat.mod_one`,
  `Nat.one_mul`, `congrArg`, `congrFun'`, and `of_eq_true`.
- Five carry `propext`: gcd commutation, both general subtraction/multiplication
  equations, `Nat.mod_self`, and `eq_self`.
- Two carry the quotient axioms without `propext`: `Nat.gcd_succ` and the
  private gcd equation.

This proves that generic equality congruence is not the problem. The
contamination lies in the official gcd/divisibility and selected
proposition-normalization routes.

## Route pruning

A subtraction-only Bézout induction does not need `Nat.mod_self`, `eq_self`, or
`Nat.gcd_succ`. Retaining only the zero-left base and the two subtraction
steps leaves four assumption-bearing carriers:

- `Nat.gcd_comm`;
- `Nat.gcd_sub_mul_right_left`;
- `Nat.gcd_sub_mul_right_right`;
- `_private.Init.Data.Nat.Gcd.0.Nat.gcd.eq_1`.

Their exact previously unmeasured direct frontier has seven names: four gcd
divisibility lemmas, the addition/multiplication gcd equation,
`Nat.sub_add_cancel`, and the private gcd definition equation. The subtraction
carrier was already independently localized and replaced earlier, so the next
measurement must bind that prior evidence rather than rediscover it.

No replacement source was compiled and no theorem or ledger credit was issued.

## Immutable evidence

The read-only pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/38e40236f-subtractive-gcd-dependency-audit-v1/manifest.json`

Its manifest SHA-256 is
`f93cd95d1126efbcc028b57e051441ced525d2ef4a321b6e352ce099f2fc6b4c`.

## Verification

```sh
python3 scripts/check-autogenesis-subtractive-gcd-dependency-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_subtractive_gcd_dependency_audit_result
```
