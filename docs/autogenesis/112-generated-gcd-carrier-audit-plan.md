# Generated gcd carrier audit plan

Date: 2026-08-21

## Decision

Classify the sole generated theorem beneath the private official gcd equation:

```text
_private.Init.Data.Nat.Gcd.0.Nat.gcd._unary.eq_def
```

The theorem is already present in the sealed export, so the measurement needs
zero exporter invocations and one importer read. It emits only the carrier's
canonical identity, direct theorem dependencies, and kernel-derived footprint.

## Architectural fork

If the direct closure localizes to generic well-founded equation machinery, a
later plan may replace the equation by primitive bounded reasoning while
retaining official gcd as the statement surface. A broader contaminated
closure favors an explicit target-owned gcd and a later semantic bridge.

This pass authorizes neither option. It renders no proof material and grants no
reconstruction, theorem, target, evaluation, fact, or ledger authority.

## Verification

```sh
python3 scripts/check-autogenesis-generated-gcd-carrier-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_generated_gcd_carrier_audit_plan
```
