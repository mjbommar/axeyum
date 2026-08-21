# Rooted xgcd projection reconstruction plan

Date: 2026-08-21

## Decision

Correct the measured execution boundary without changing the theorem source.
The byte-identical `rfl` candidate is copied once to the exact module filename
under the pinned Mathlib package root, compiled once, and exported only if that
compilation succeeds. Axeyum then independently imports the authored theorem
twice; both rows must agree and be empty-footprint with no direct theorem
dependencies.

The shared checkout is a reference environment, so the control is two-sided:
it must be clean before the copy, all three named temporary paths must be absent,
and it must be clean again after removing exactly the source, olean, and ilean
created by this increment. No broader cleanup is authorized.

This is a new preregistered experiment, not a retry hidden inside the failed
one. It still grants no projection theorem, extended-gcd, fact, or ledger credit
until its evidence is frozen in a separate result.

## Verification

```sh
python3 scripts/check-autogenesis-xgcd-val-rooted-reconstruction-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_xgcd_val_rooted_reconstruction_plan
```
