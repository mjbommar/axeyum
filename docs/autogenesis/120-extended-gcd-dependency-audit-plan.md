# Extended-gcd direct-dependency audit plan

Date: 2026-08-21

## Decision

Classify all twelve direct theorem dependencies of the assumption-bearing
official `Nat.gcd_eq_gcd_ab` root. The exact order is inherited from the first
batch audit. The coefficient core of interest is:

```text
Nat.xgcdAux_val
Nat.xgcd_val
_private.Mathlib.Data.Int.GCD.0.Nat.xgcdAux_P
```

The nine remaining roots are measured too; treating familiar equality and
integer arithmetic names as clean without asking the kernel would repeat the
ledger error this programme is designed to prevent.

The twelve declarations already exist in the immutable root-selected export,
so this increment permits zero exporter invocations and exactly one batch
importer read. Proof terms, theorem types, theorem values, and raw NDJSON remain
hidden from model context.

If all three coefficient-core roots are empty-footprint, the next increment may
preregister an explicit reconstruction from the measured interface. If any is
assumption-bearing, the next increment may descend only its novel direct
dependencies. Neither successor is authorized here.

## Verification

```sh
python3 scripts/check-autogenesis-extended-gcd-dependency-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_extended_gcd_dependency_audit_plan
```
