# Generated gcd carrier audit result

Date: 2026-08-21

## Result

The generated official gcd equation carrier has the expected quotient
footprint and six direct theorem dependencies. Three—`Eq.trans`, `congrArg`,
and `congrFun'`—were already measured as empty-footprint. The exact novel
frontier is:

- `WellFounded.Nat.fix_eq`;
- the private gcd termination proof `_unary._proof_1`;
- the generated `PSigma.casesOn._arg_pusher`.

This is a bounded compiler-generated seam, not an unbounded mathematical
closure. It still requires one final classification pass: the termination
proof and argument pusher must not be assumed clean merely because the generic
fix equation is the likely carrier.

No proof material was rendered, no reconstruction was attempted, and no
theorem or ledger credit was issued.

## Immutable evidence

The read-only pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/38e40236f-generated-gcd-carrier-audit-v1/manifest.json`

Its manifest SHA-256 is
`9f18edbf8cc990e0f4e62910e9b06e836fc2809d4501ea2d3e07e3b3495d994b`.

## Verification

```sh
python3 scripts/check-autogenesis-generated-gcd-carrier-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_generated_gcd_carrier_audit_result
```
