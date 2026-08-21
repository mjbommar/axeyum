# Exact `Int.fib_neg` dependency audit plan

Date: 2026-08-21

## Decision

Classify all 26 direct theorem dependencies measured for official
`Int.fib_neg` in one ordered, non-rendering reread of its immutable export.
This replaces source-level guessing with kernel-derived evidence and preserves
the exact frontier, including generated parity and conditional helpers.

The pass uses the already sealed 14,596,588-byte stream. It performs no new
export, renders no proof material, submits no theorem, and changes no fact.
The result may only choose whether the smallest reconstruction can use clean
dependencies directly or must replace a required assumption-bearing
mathematical root through a further preregistered descent.

## Verification

```sh
python3 scripts/check-autogenesis-int-fib-neg-dependency-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_int_fib_neg_dependency_audit_plan
```
