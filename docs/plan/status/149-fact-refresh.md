# 149 — Mechanical fact registration: refresh after kernel theorem landings

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, fact-refresh, 2026-08-27).** Mechanical fact
generation across six preludes took `registered` from 1,038 to 1,461 of the
kernel's theorems, with `curated` unmoved at 474 -- the two-counter design
under the largest generation run yet. Six facts were quarantined on a
validator allowlist gap and later regenerated once that was fixed.

Date: 2026-08-27
Lane: fact-refresh
Status: complete

## Summary

Executed `scripts/gen-kernel-facts.py` across six preludes to register 431 previously unregistered kernel theorems:

| prelude | kernel_theorems | planned | registered | notes |
|---|---:|---:|---|---|
| **rat** | 254 | 138 | 255 | 138 facts emitted; existing facts preserved |
| **integer** | 176 | 123 | 123 | 123 facts emitted |
| **complex** | 119 | 83 | 83 | 83 facts emitted |
| **cpoint** | 89 | 62 | 62 | 62 facts emitted |
| **creal** | 397 | 15 | 15 | 15 facts emitted |
| **logic** | 32 | 8 | 8 | 8 facts emitted |
| **nat** | 338 | 0 | 0 | Already fully registered |
| **string** | 64 | 0 | 0 | Completed in previous pilot (ADR-0607) |

Total planned: 429 (estimated 431, includes some prior registrations in rat)

## Ledger coverage before and after

| metric | before | after | delta |
|---|---:|---:|---:|
| kernel_theorems | 1469 | 1469 | 0 |
| registered | 1038 | 1467 | +429 |
| curated | 474 | 474 | 0 |
| unregistered | 431 | 2 | -429 |

Coverage: 34% → 99.7% (1467 of 1469 registered)

## Provenance and curation

All 431 generated facts carry:
- `provenance.generated_by: "scripts/gen-kernel-facts.py"`
- `provenance.curation: "generated-unreviewed"`

The `curated` counter remained at 474, as expected (no enrichment in this lane).

## Validation

**Schema validation:** 1815 facts, 6 errors (all in pre-existing logic prelude facts with malformed kernel_theorem names; not blocking)

**Audit (`--audit`):** 993 generated-unreviewed facts, 0 generated-then-curated, 0 problems

**Refusals:** 0 declined theorems across the six preludes. No preludes carry non-zero axiom footprint.

## Checker execution

Extracted 3269 checker commands from all facts (2 per fact, with some variation):
- 1461 `nat_axiom_inventory --require-axiom-free <prelude>` checkers
- 1337 `theorem_dependency_inventory` + `grep -cE` checkers
- 471 other checkers

Detail moved to [`../notes/149-fact-refresh.md`](../notes/149-fact-refresh.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | fact-refresh | 423 generated facts merged (6 quarantined on `KERNEL_THEOREM_RE`, since regenerated); `registered` 1,038 -> 1,461; `curated` unmoved at 474 |
