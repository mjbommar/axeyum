# Exact `Int.fib_neg` root audit result

Date: 2026-08-21

## Result

The preregistered root-selected export and non-rendering importer pass each ran
exactly once. The official Mathlib 4.30 theorem `Int.fib_neg` is not directly
admissible: its kernel footprint contains `Classical.choice`, `propext`, Lean
opaque/string support, and the quotient primitives. No reconstruction, theorem
credit, fact-status change, or ledger write occurred.

The measurement exposes 26 direct theorem dependencies. Most are equality,
conditional, parity, sign, and arithmetic support; the central mathematical
bridge is `Int.fib_neg_natCast`, with `Int.eq_nat_or_neg` providing the integer
case split. The next bounded increment must classify these exact 26 roots in
one non-rendering reread of the already sealed stream. That will distinguish
clean reusable leaves from automation-generated assumption carriers.

## Durable evidence

The immutable reference pack is
`/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-root-audit-v1/`.
The proof-bearing stream is 14,596,588 bytes with SHA-256
`7df7f5dce9c7159f9c468b6f47f13be3e589fb2c1559af554ce73cc48b18730e`;
it was never rendered into model context. The pack manifest is SHA-256
`c1ba7157b8f644bbfda48d4db4b4e528eb2705bd7600f0f033304d678f48f3fd`.

## Verification

```sh
python3 scripts/check-autogenesis-int-fib-neg-root-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_int_fib_neg_root_audit_result
```
