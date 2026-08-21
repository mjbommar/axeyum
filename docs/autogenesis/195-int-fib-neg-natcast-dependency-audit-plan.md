# `Int.fib_neg_natCast` dependency audit plan

Date: 2026-08-21

## Decision

Classify the exact 36 direct theorem dependencies beneath the assumption-bearing
negative-natural Fibonacci core. The clean outer integer case split is retained;
this pass descends only through the remaining mathematical obstruction.

The existing sealed stream is read once by the non-rendering batch auditor.
There is no export, proof exposure, theorem submission, fact mutation, or ledger
write. The measurement may only select the smallest parity/sign recurrence core
and identify which indispensable contaminated leaves require target-owned
replacement.

## Verification

```sh
python3 scripts/check-autogenesis-int-fib-neg-natcast-dependency-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_int_fib_neg_natcast_dependency_audit_plan
```
