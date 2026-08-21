# Baseline-preserving xgcd projection reconstruction plan

Date: 2026-08-21

## Decision

Run the byte-identical `rfl` projection candidate while preserving the exact
three-file untracked baseline discovered by preflight. The baseline is bound by
ordered path, status, size, mode, and SHA-256. Its files remain unreadable to
the model and may not be changed or removed.

Before execution, the three planned temporary names must be absent and the full
checkout status must equal the baseline exactly. The source may then be copied
once under the package root and compiled once. Export occurs only on success;
Axeyum independently imports twice. Cleanup removes exactly our source, olean,
and ilean, after which the full status and all three baseline hashes must match
again.

No retry, theorem credit, extended-gcd reconstruction, fact mutation, or ledger
write is authorized.

## Verification

```sh
python3 scripts/check-autogenesis-xgcd-val-baseline-preserving-reconstruction-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_xgcd_val_baseline_preserving_reconstruction_plan
```
