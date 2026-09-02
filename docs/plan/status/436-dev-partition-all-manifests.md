# Lane: dev-partition-all-manifests — fix two v1-only nursery readers (gate-hygiene lane 2)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, dev-partition-all-manifests, 2026-09-02).** Fixing
`check-development-partition.py` (reads `nursery-v1.json` alone, missed the
four development facts `authoritative-mathlib-nat-bit-constructor-family-v1`
closed in `nursery-v2-extension.json`) and
`test_check_autogenesis_holdout_isolation.py`'s pinned `held_out=206` literal
(live count is 226 after draw 19). In progress.

<!-- plan-section: landed-changes -->

