# Full Mathlib statement-survival atlas plan

Date: 2026-08-20

## Known before the plan

The two immutable statement inventories have 9,712 names in common. Seventeen
v4.30.0 names are absent from v4.32.1, and v4.32.1 adds 110 names. These name
counts were observed before this plan and are not presented as preregistered
outcomes.

The structural identity distribution across the 9,712 shared names has not yet
been measured. This plan freezes that remaining pass before computing it.

## Fixed comparison

Every name in the union will receive exactly one row in an external read-only
delta. Shared rows are classified as structurally identical, module-only drift,
pretty-type-only drift, or structural drift. Removed and added names receive
separate classes. Structural drifts record exact constant-multiset additions
and removals.

The tracked atlas will aggregate class counts by Nat/Int domain and module
transition and retain all 127 added/removed names. The existing 240-candidate
comparison must equal the atlas projection exactly; the broad measurement
cannot rewrite or reselect the frozen nursery.

## Authority

One structural comparison pass is permitted, with no extraction, retry, policy
adaptation, proof access, theorem value, proof search, kernel submission,
executor call, fact transition, evaluation credit, or ledger write.

The row-level delta remains external. Git receives only its identity, aggregate
atlas, generator, checker, tests, and documentation.

## Verification

```sh
python3 scripts/check-autogenesis-mathlib-full-statement-survival-atlas-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_mathlib_full_statement_survival_atlas_plan
```
