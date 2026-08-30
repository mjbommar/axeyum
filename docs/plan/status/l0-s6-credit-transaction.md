# Lane: l0-s6-credit-transaction — ADR-0717 L0 phase S6, the atomic credit transaction

<!-- plan-section: lane-status -->

**Done, l0-s6-credit-transaction, 2026-08-30.** [ADR-0785](../../research/09-decisions/adr-0785-credit-transactions-two-phase-commit-with-a-crash-sweep-that-actually-crashes.md)
records the full measurement. Summary:

`scripts/credit-transaction.py` is a fault-injectable two-phase-commit engine
over a self-contained fixture ledger (`facts/`, `receipts/`, `pins/`,
`graph/`, `dashboards/`) — deliberately NOT wired into the real
`artifacts/facts/` flip in this phase, since that surface
(`scripts/validate-facts.py`, the real pins file) belongs to other lanes;
scope here was the transaction mechanism and its verification.

Measured, not asserted:

Detail moved to [`../notes/l0-s6-credit-transaction.md`](../notes/l0-s6-credit-transaction.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | l0-s6-credit-transaction | Crash-safe two-phase-commit engine (`scripts/credit-transaction.py`) + gate (`scripts/check-credit-transaction.py`) + 27-test suite + 9-guard mutation table (`scripts/tests/test-credit-transaction*`), registered in justfile and check.sh; ADR-0785. |
