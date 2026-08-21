# Subtractive gcd route-frontier audit result

Date: 2026-08-21

## Result

All six selected roots are assumption-bearing. Five carry `propext`; the
private official gcd definition equation carries the four quotient axioms.
Its sole direct theorem dependency is the generated carrier:

```text
_private.Init.Data.Nat.Gcd.0.Nat.gcd._unary.eq_def
```

The failure is therefore inside the well-founded compilation boundary of the
official gcd definition, not merely in public convenience wrappers. The four
gcd divisibility routes also remain contaminated through gcd recursion,
modulo, or proposition equality.

## Consequence

The subtraction strategy is not yet rejected as mathematics, but it cannot
advance by importing the official equation stack. One final narrow diagnostic
can classify the generated `_unary.eq_def` carrier's direct dependencies. If
that localizes to generic well-founded fix congruence, the constructive option
is a primitive bounded proof of the official gcd equation. Otherwise the
cleaner architecture is a target-owned gcd with an explicit later semantic
bridge.

The already reconstructed primitive subtraction restoration remains valid and
reusable. No new proof was compiled and no theorem or ledger credit was issued.

## Immutable evidence

The read-only pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/38e40236f-subtractive-gcd-route-frontier-audit-v1/manifest.json`

Its manifest SHA-256 is
`cd13ae221f70309ec586a1ace4f664b72404fb957325949b2d8d2f1a747b60b2`.

## Verification

```sh
python3 scripts/check-autogenesis-subtractive-gcd-route-frontier-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_subtractive_gcd_route_frontier_audit_result
```
