# Lane: ledger-regen — regenerate the four stale generated ledgers and decide merge-blocking

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, ledger-regen, 2026-09-01).** All four generated
ledgers regenerated and their `--check`s green: `theorem-production-ledger.md`
(1,448 -> 2,340 distinct theorems), `production-provenance-ledger.md` (2,054
-> 2,343 established facts, multi-target unchanged at 30),
`artifacts/import-backlog.json` (147 -> 213 rows), `artifacts/ledger-
coverage.json` (kernel_theorems 2,340, registered 2,063, unregistered 277).
Root cause of the staleness: the kernel grew an `ipc` (intuitionistic
propositional calculus) prelude group on 2026-08-31 that neither generator's
coverage list knew about — `gen-theorem-production-ledger.py`'s own
fail-closed guard caught it correctly (`coverage changed`) the first time
this lane ran it; fixed `EXPECTED_PRELUDES` and `gen-ledger-coverage.py`'s
`prelude_of()` namespace map.

ADR-1511 decides the merge-blocking question: none of the four `--check`s
ran in `hooks/pre-push` or CI before this lane; all four were only wired
into `scripts/check.sh`/`just check` (~10 min, not run per merge).
`gen-import-backlog.py --check` and `gen-production-provenance-ledger.py
--check` (~0.1s each, no cargo) now run for real in
`scripts/check-merge-hygiene.sh`. `gen-theorem-production-ledger.py --check`
and `gen-ledger-coverage.py --check` (~40s warm / ~3min cold — both shell
out to a release kernel build) stay in the full gate, but
`check-merge-hygiene.sh` gained a cheap cross-consistency ratchet comparing
the two ledgers' theorem counts against each other (no cargo). Discriminating
test both directions confirmed for the ratchet and for import-backlog: corrupt
the committed count -> gate exits 1 naming the mismatch; restore -> exits 0.

`scripts/flywheel-status.sh`'s PRODUCTION panel now prints the git-log date
of `theorem-production-ledger.md` beside the theorem count.

Did not run: `cargo test` (excluded by brief). Did not implement: path-
conditioning the two expensive checks into `pre-push` (left as a named
Alternative in ADR-1511 — a larger change than this lane's scope; the
cross-consistency ratchet already closes the specific drift this lane found).

<!-- plan-section: landed-changes -->

| 2026-09-01 | ledger-regen | status stub committed |
| 2026-09-01 | ledger-regen | fixed ipc-prelude coverage gap in two generators; regenerated all four stale ledgers (theorem-production 1,448 -> 2,340; provenance 2,054 -> 2,343; import-backlog 147 -> 213; ledger-coverage kernel_theorems 2,340) |
| 2026-09-01 | ledger-regen | ADR-1511: import-backlog and production-provenance --checks now block in check-merge-hygiene.sh; added a cross-consistency ratchet for the two cargo-dependent ledgers; flywheel-status.sh PRODUCTION panel now shows the ledger's last-regenerated date |
