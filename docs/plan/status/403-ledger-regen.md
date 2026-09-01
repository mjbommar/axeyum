# Lane: ledger-regen — regenerate the four stale generated ledgers and decide merge-blocking

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, ledger-regen, 2026-09-01).** Starting task: regenerate
`theorem-production-ledger.md`, `production-provenance-ledger.md`,
`artifacts/import-backlog.json`, `artifacts/ledger-coverage.json`, each of which
was stale and whose `--check` was red on main. Also writing ADR-1511 on which
`--check` should block a merge and by what mechanism, and fixing
`scripts/flywheel-status.sh` to stop reprinting the stale headline number.
Status stub committed first per lane protocol; details land here as work
completes.

<!-- plan-section: landed-changes -->

| 2026-09-01 | ledger-regen | status stub committed; regeneration in progress |
