# Lane: kernel-receipt — a general kernel-lane execution driver for operation receipts

<!-- plan-section: lane-status -->

**Closed the "no shape for hand-authored kernel proof" gap doc 293 hit**
(`DONE`, kernel-receipt, 2026-08-27). Doc 293 proved five `Int.ModEq`
theorems directly against the kernel (no producer/import pipeline component
running at all) and could not register the retrospective receipt ADR-0602
calls for: `validate-autogenesis-operations.py`'s `EXECUTION_DRIVERS` was a
closed set of ten, eight of them `axeyum-lean-import/*` (pipelined) and two
named for one-off episodes. Per doc 288, 125 of 132 dependency-ready facts
are exactly this `proof-route-only` shape, so this was not a corner case.

Added `axeyum-lean-kernel/authored-declaration-v1` in
`scripts/validate-autogenesis-operations.py`: fields chosen to be
independently re-checkable (declaration name(s), the source file each must
literally appear in, and the exact test functions that must exist and fail
on their absence) rather than narrative. Registered doc 293's five closures
as ONE operation (`authoritative-kernel-int-modeq-shift-family-v1`) naming
all five facts, per the standing "`applicability.fact_ids` is a list, never
required length one" rule (doc 228). Full account:
[`docs/autogenesis/296-a-general-kernel-lane-execution-driver.md`](../../autogenesis/296-a-general-kernel-lane-execution-driver.md).

Detail moved to [`../notes/kernel-receipt.md`](../notes/kernel-receipt.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | (pending) | New `axeyum-lean-kernel/authored-declaration-v1` execution driver in `scripts/validate-autogenesis-operations.py` (re-checkable fields: declaration source/test file existence, literal declaration-in-source check, literal test-function-in-file check, fact-id binding order); registered doc 293's five `Int.ModEq` closures as one operation; ten discrimination tests + eight mutation-verified guards; ADR-0602 amendment; `docs/autogenesis/296`; regenerated `docs/plan/generated/production-provenance-ledger.md`. |
