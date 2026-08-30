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

- **Crash sweep**: one full transaction performs 26 low-level write ops.
  Re-running with a fault injected at each of the 26 and then calling
  `recover()` converges to byte-identical OLD or NEW ledger state at every
  single one — never neither. The gate fails closed if the sweep ever finds
  zero boundaries or if either outcome never occurs.
- **Fresh read**: `commit()` re-reads the journal from disk rather than the
  in-process object staging returned. Demonstrated by planting a sentinel
  directly into the on-disk journal's `txn_id` field (a field no staleness
  check reads, chosen so this is independent of the other four guards) and
  confirming `commit()` preserves it rather than clobbering it with the
  cached value.
- **Four staleness dimensions**, four distinct exception classes:
  `StaleReceiptError`, `StaleSourceError`, `StaleGraphError`,
  `StaleCheckerError`. Each has its own fixture that is stale along exactly
  one dimension while the other three stay fresh; a fifth, fully-fresh
  fixture must commit without rejecting.
- **Idempotent replay**: an `applied.json` registry short-circuits a repeat
  `(fact_id, receipt)` before the cascade is even recomputed. A companion
  test calls `propose/commit/apply` directly, twice, WITHOUT the guard, and
  confirms a real duplicate cascade/dashboard entry — proving the guard is
  load-bearing, not decorative.
- **Mutation table**: 9 guards (fresh-read, 4 staleness checks, commit/apply
  state preconditions, corrupt-staging refusal, idempotence short-circuit),
  each deleted in a scratch copy (`scripts/tests/test-credit-transaction-mutations.sh`,
  never the shared checkout), each killing EXACTLY its own designated canary
  from a disjoint set of nine narrow tests. Full table in ADR-0785.
- **Fails on absence**: `--empty-fixtures` / `--empty-boundaries` each exit 1
  with a named reason, checked at both the function and subprocess level.

27 tests in `scripts/tests/test-credit-transaction.py`, all green. Registered
in both `justfile` (the `facts:` recipe) and `scripts/check.sh` as
`credit-transaction`, `credit-transaction-tests`,
`credit-transaction-mutations`.

**What this transaction does NOT make atomic**, stated plainly: a receipt
recorded via `record_latest_receipt()` OUTSIDE any transaction (the exact
mechanism the stale-receipt fixture uses to simulate a concurrent lane) is,
by construction, not itself covered by any transaction — it is the external
"a checker already validated this" event that staleness checking exists to
detect changes to, not something this mechanism protects.

**Next step for another lane**: wire this engine into the real fact-flip
path (`artifacts/facts/<id>.json`, `artifacts/ontology/settled-fact-statement-pins.json`,
the generated dashboards) — that requires touching `scripts/validate-facts.py`
and files this lane's scope excluded.

<!-- plan-section: landed-changes -->

| 2026-08-30 | l0-s6-credit-transaction | Crash-safe two-phase-commit engine (`scripts/credit-transaction.py`) + gate (`scripts/check-credit-transaction.py`) + 27-test suite + 9-guard mutation table (`scripts/tests/test-credit-transaction*`), registered in justfile and check.sh; ADR-0785. |
