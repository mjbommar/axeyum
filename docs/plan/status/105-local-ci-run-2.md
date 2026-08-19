# Lane: local-ci-run-2 — the authoritative gate is green, and now it is enforced

<!-- plan-section: lane-status -->

**`scripts/local-ci.sh --record` PASSED at `57af69142`, and
`check-local-ci-freshness` is now ENFORCING at both call sites** (`DONE`,
local-ci-run-2, 2026-08-19). Record: `artifacts/local-ci-runs/57af69142-s4.json`
— 5/5 steps `pass`, rc=0, 6656 s wall. Steps: fmt 4 s · stable clippy
`-D warnings` 29 s · MSRV 1.88 check 15 s · `cargo nextest --profile local
--workspace --all-features` **7561 tests run, 7561 passed** (87 slow, 32
skipped) in 6588 s · doctests **179 passed** in 20 s. Zero `FAIL [` lines in
the run log, cross-checked against the record rather than read off the exit
code. The four golden-pin failures in the first record (`a6ee37c6a`, FAIL
rc=100) were genuinely fixed by `31442bd5d`; nothing else regressed, and the
suite grew 7511 → 7561 tests in between.

**The `tests: -1` bug is confirmed fixed by measurement, not by reading the
patch**: the old record recorded `-1` for the 7511-test sweep (nextest indents
its `Summary` five spaces, the pattern was `^`-anchored), so the vacuous-step
guard could not fire on the one step it exists for. This record reads 7561.

**Flipped to enforcing** in `scripts/check.sh` and the `justfile`'s
`local-ci-freshness` recipe (plus the checker's own header, which still
described itself as report-only). Then proved the enforcing call site's exit
status depends on the finding, through `just`, not just through the control
suite: empty record dir → rc=1 `NO_RECORD`; a copy of this record with
`finished_utc` backdated 5 days → rc=1 `STALE: 120h`; the nextest step
rewritten to `vacuous` → rc=1 naming that step. All 9 controls green.

**Standing cost this imposes on every lane:** the sweep is ~110 min behind one
box-wide lock and the budget is 48h, so roughly one lane per day must run
`scripts/local-ci.sh --record` and commit the record. It needs `setsid` — a
foreground shell caps at 10 min and an ordinary background job was killed at
59 m 59.9 s with no record written (the recorder only writes at the end).

Detail: [`../notes/105-local-ci-run-2.md`](../notes/105-local-ci-run-2.md).

<!-- plan-section: landed-changes -->

| 2026-08-19 | (pending) | `artifacts/local-ci-runs/57af69142-s4.json`: first all-pass authoritative-gate record (5/5 steps, 7561+179 tests, 6656 s); `check-local-ci-freshness` flipped from `--report-only` to ENFORCING in `scripts/check.sh` and `justfile`. |
