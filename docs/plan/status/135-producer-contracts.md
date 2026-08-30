# Lane: producer-contracts — ADR-0602 prospective producer-contract artifact

<!-- plan-section: lane-status -->

**ADR-0602 implemented (`done-for-now`, producer-contracts, 2026-08-27).**
Doc 288 diagnosed `fact-frontier.py --json` reporting `admissible: 0` over 132
dependency-ready facts as structural, not a registry gap: the operation
registry's `ADMISSION_CONTRACTS` requires `epistemic_status: "proved"` on
every arm, so it cannot represent "we could attempt this open fact" without
fabricating a proof that does not exist. ADR-0602 decided the fix: a separate,
prospective producer-contract artifact (a capability claim, never a
completion claim) that `fact-frontier.py` selects against alongside the
operation registry.

Detail moved to [`../notes/135-producer-contracts.md`](../notes/135-producer-contracts.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `PENDING` | Implemented ADR-0602: `artifacts/ontology/producer-contract.schema.json` + `scripts/validate-producer-contracts.py` (a capability claim, never a completion claim — no `proved`/`epistemic_status` field exists in the schema at all), two seed contracts (Int.ModEq congruence family, Nat.Coprime family — both checked held-out-clean against `nursery-v1.json`), and redefined `fact-frontier.py` admissibility as dependency-ready × (registered operation OR matched capable-route contract). `admissible_count` moved 0 → 27 on the real ledger; all 8 existing `test_fact_frontier.py` tests pass unmodified, 7 new added. `docs/autogenesis/289-producer-contract-admissibility.md`. |
