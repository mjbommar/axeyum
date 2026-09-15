# Lane: ledger-structure — does the ledger show dispatch structure worth deriving into Phase 4?

<!-- plan-section: lane-status -->

**Lane ledger-structure (`WIP`, ledger-structure, 2026-09-15).** Phase 3
sizing for Phase 4 of
[dispatch-and-instrumentation-2026-09-15.md](../dispatch-and-instrumentation-2026-09-15.md#5-phase-4--derived-ladder-policy-conditional).
Fills the outcome ledger (ADR-2102, ADR-2105) over all seven Tier 1 pinned
200-file lists on `db31113fa`, 24 s / 8 GiB, `--trace` on, sharded 3 hosts x 4
core pairs (12 shards, `bench-results/ledger-structure-20260915/
launch-t1-ledger-sweep.sh`). In flight; next step is consolidation into
`bench-results/ledger/` through `outcome_ledger.py`, then the per-class,
per-division structure tables in
`bench-results/ledger-structure-20260915/README.md`.

No Rust, no ADR — this lane answers one measurement question from the ledger
the Phase 3 lane already built.
