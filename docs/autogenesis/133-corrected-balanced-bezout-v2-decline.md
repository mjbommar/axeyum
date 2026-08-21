# Corrected balanced-Bézout V2 compilation decline

Date: 2026-08-21

## Result

V2 consumed its one main-source compilation and stopped before export or
import. The direct `Nat.mod` correction removed V1's equation-pattern failure,
and coefficient-scoped transport avoided rewriting the gcd remainder. Lean then
localized four remaining elaboration errors into three classes:

1. unfolding `Nat.modCore` exposes a dependent conditional on divisor
   positivity before reaching `Nat.modCore.go`;
2. `congrArg` retains lambda beta-redexes unless its result is given an explicit
   normalized product type; and
3. the induction hypothesis's `%` and `m + 1` notation is definitionally equal
   to, but not syntactically the same as, the direct `Nat.mod`/`m.succ` calc
   context.

V3 may eliminate the conditional with the already available `0 < m` proof,
type both lifted equalities explicitly, and use `change` on the induction
hypothesis before the contextual rewrite. No mathematical route change is
indicated.

The sealed evidence manifest is
`/nas3/data/axeyum/autogenesis/reference-packs/1de1558f7-official-gcd-balanced-bezout-v2-v1/manifest.json`,
SHA-256 `d5532817d252b359fb7a9fb01324c48b619ad64d8e79b3208fbba3b084c055a0`.
The exact six temporary paths were removed and the three-file `s5` baseline is
unchanged. There were zero exports, imports, proof-stream reads, retries, or
theorem/target/ledger credits.

## Verification

```sh
python3 scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-result-v2.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_reconstruction_result_v2
```
