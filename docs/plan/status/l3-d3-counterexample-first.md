# Lane: l3-d3-counterexample-first — D3 counterexample-first definition review

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, l3-d3-counterexample-first, 2026-08-30).** D3's
falsification screen is landed and gated: 2 retained false statements over
the bitwise-fuel family (new relative to S3's 13 fixtures), 6 definitions
reviewed against independent references with 1 mutation each (every mutation
verified to move an observation, none vacuous), 2 review obligations for
unexecutable `CReal` constructions, 10 screen receipts, and 1 real demo
dispatch entry whose ordering is checked against actual git history
(`git merge-base --is-ancestor`), not simulated. 17 guards in
`scripts/check-falsification-screen.py`, all wired through one named
`GUARD_NAMES` table, all mutation-verified to kill exactly one test each
(`scripts/tests/test-falsification-screen-mutation-verify.sh`, run in a
scratch copy, never the shared checkout). 41 unit tests
(`scripts/tests/test_falsification_screen.py`), gate registered in both
`justfile` and `scripts/check.sh`. ADR-0890 records the design.
`scripts/check-autogenesis-holdout-isolation.py` run before and after: never
touched, `references=0` both times, verdict PASS. Scope stayed within
`artifacts/falsification/`, `scripts/gen-falsification-screen.py`,
`scripts/check-falsification-screen.py`,
`scripts/falsification_screen_fixtures.py` (library paired with the two
named scripts, mirroring S3's `check-X.py` + `X_fixtures.py` shape),
`scripts/tests/test_falsification_screen.py` +
`scripts/tests/test-falsification-screen-mutation-verify.sh`, ADR-0890,
`justfile`/`scripts/check.sh` (two lines each, no restructuring), and this
file.

**Note on the brief's citations.** `docs/research/09-decisions/adr-0870-*.md`
and `artifacts/effort-taxonomy/report.md` do not exist anywhere in this tree
(checked HEAD and `origin/main`, both at the same commit; no file anywhere
mentions `adr-0870` or `effort-taxonomy`). Proceeded from
`docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md`'s D3 section
and ADR-0752, which do exist, rather than fabricating content for the missing
citations.

**What this screen would still miss.** It is a Python-level model of the
Rust definitions, not the Rust kernel definitions themselves -- a defect
introduced only in the ACTUAL kernel construction, that this pack's
hand-transcribed reference happens to reproduce identically, would pass
every guard here. Closing that gap needs the screen to execute the real
kernel declarations (via a prelude build), which D3's exit criterion does
not require and this lane did not attempt.

<!-- plan-section: landed-changes -->

| 2026-08-30 | `2a5625ca7` | Refresh screen-summary.md receipt/dispatch counts (pins unchanged). |
| 2026-08-30 | `adbd89dee` | Register falsification-screen gate in justfile and check.sh. |
| 2026-08-30 | `c7d0e7588` | Named guard table + 41 unit tests; all 17 guards mutation-verified to kill exactly one test. |
| 2026-08-30 | `48c68e06c` | Real demo dispatch entry for Nat.lor; ordering verified against git log. |
| 2026-08-30 | `b6d41a7f3` | ADR-0890: falsification screen ordering read from git log. |
| 2026-08-30 | `7884497ed` | Generate screen receipts for every registered target. |
| 2026-08-30 | `9fd677073` | D3 counterexample-first screen: fixtures, gen-falsification-screen.py, check-falsification-screen.py. |
