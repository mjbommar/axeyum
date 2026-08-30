# Status: Ledger Coverage Split (Registered vs. Curated)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, ledger-ratchet, 2026-08-27).** Ledger coverage
now reports two counters instead of one: `registered` (538) and `curated`
(474). Generation moves the first and provably cannot move the second, so
bulk-generating fact skeletons is permitted and visible rather than able to
masquerade as human curation. Four mutation controls pin the independence
(4/4 guards killed, 33-test baseline).

**Track:** Refactor 2026-08-27  
**Phase:** Implement ADR-0607 measurement infrastructure  
**Date:** 2026-08-27

## Summary

Added `curated` counter to `scripts/gen-ledger-coverage.py` alongside the existing `registered` count. Both counters are independent and can move separately, enabling a ratchet structure that prevents bulk generation from masquerading as curation while remaining visible and accounted for.

## Delivered

### Code Changes

- **`scripts/gen-ledger-coverage.py`**
  - Added `is_curated()` helper: determines if a fact is curated based on provenance
  - Updated `JoinResult` class to track curated facts separately
  - Modified `join()` to populate both `registered` and `curated` dictionaries
  - Updated `build_document()` to report curated counts per-prelude and in overall summary
  - Output now includes `curation_convention` field documenting the choice made

### Measurement

**Baseline (2026-08-27):**
- kernel_theorems: 1,402 (all theorems in the kernel)
- registered: 538 (facts claiming a kernel theorem)
- curated: 474 (of the 538, the hand-written ones)
- unregistered: 864 (kernel theorems with no registered fact)

**Curation Convention:** `absent-field-is-curated`

Facts are counted as curated if their `provenance.curation` field is NOT equal to `"generated-unreviewed"`. This includes:
- Facts with no `curation` field (hand-written facts, 818 in the ledger)
- Facts with `curation` set to any value other than `"generated-unreviewed"` (enriched facts)

Facts with `curation="generated-unreviewed"` are counted as unreviewed (64 total).

**Justification for the convention:**
The `curation` field exists specifically to mark generated facts. Hand-written facts predate this field and carry no marker because they were never generated. The conservative assumption is that hand-written facts are curated unless explicitly marked otherwise. This choice affects ~93% of the ledger (818 of 882 facts), so it is explicitly documented in the output.

Detail moved to [`../notes/142-ledger-ratchet.md`](../notes/142-ledger-ratchet.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | ledger-ratchet | `registered`/`curated` split in `scripts/gen-ledger-coverage.py`; convention `absent-field-is-curated` printed in the output; 4 mutation controls in `mutation_controls.py`; 7 tests in `test_gen_ledger_coverage.py` |
