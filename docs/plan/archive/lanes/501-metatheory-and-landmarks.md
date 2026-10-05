# Lane: metatheory-and-landmarks — kernel metatheoretic status (W0-4) and the landmark count (W1-4)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, metatheory-and-landmarks, 2026-09-04).** Both
deliverables landed. Documentation and one script only — no kernel
declarations, no theorems, per brief.

**W0-4, ADR-1600.** Trusted core re-measured at 5,526 function-body lines
across 9 files / 256 of 8,374 functions (`scripts/check-kernel-trusted-core.py`,
call-graph closure from the 4 admission gates — up from 5,148 on 2026-08-17).
Eight declaration kinds; confirmed absent from the trusted core: `Quot.sound`,
`funext`, `propext`, choice. Four soundness-critical guards mutation-tested
in an isolated `scripts/lane-snapshot.sh` copy, restored byte-identical: 3
fire cleanly on a specific, narrow test set (strict positivity, `Prop`
large-elimination, universe-parameter binding); 1 (the nested-inductive
phantom-parameter domain check) found to currently have NO test that depends
on it specifically — a downstream restoration check independently catches
every fixture in the suite — reported as an open, scoped finding for a lane
that owns `inductive.rs`, not fixed here. `scripts/check-lean-gate.sh` run in
full against the 4.34.0-rc1 pin: reproduced the one known-red mutant
(`real_lean_wire_differential`, `level.max-kind:1322:max-to-imax`) first-hand
with its exact panic output (291 mutants checked, 1 violation, `stricter_than_lean=0`).
Section 5 states what a relative consistency/normalization/model-soundness
result would need and why none is attempted inside this kernel (Gödel's
second incompleteness theorem).

**W1-4, landmark count.** Rule: `epistemic_status == "proved"` and title not
`[generated]`-prefixed. Measured: 2,758 total facts, 2,487 proved, 1,055
generated, **1,432 landmarks** (57.6% of proved). `scripts/count-landmark-facts.py`
exits 2 on a malformed ledger regardless of `--check`; `--check` compares to
a committed baseline and names the mismatched field on drift.
`scripts/tests/test_count_landmark_facts.py`: 9 guards, 17 tests; an ad hoc
mutation driver (restored byte-identical) found 5 of 8 mutations kill
exactly one test and 3 kill 2-3 (shared classification/loading helpers used
by multiple test classes — reported as measured, not forced to look
artificially 1:1). Registered in `scripts/check.sh`
(`landmark-facts`/`landmark-facts-controls`) and the `justfile`'s `facts`
recipe; both steps confirmed non-inert by direct invocation (exit 0). Note:
`just facts` itself is currently red on an unrelated, pre-existing step
(`gen-safety-matrix.py --check`, stale from other lanes' ledger changes)
that this lane does not own and did not touch.

**Gates run:** `python3 scripts/validate-facts.py` (0 errors, exit 0);
`python3 -m unittest scripts.tests.test_count_landmark_facts` (17/17);
`python3 scripts/gen-adr-index.py --check` (clean after regen);
`python3 scripts/gen-plan.py --check` (clean after regen);
`bash scripts/check-links.sh` (clean); `bash scripts/check-merge-hygiene.sh`
(PASS). Did NOT run: the non-kernel portion of `scripts/check-lean-gate.sh`
(`lean_crosscheck` and the `*_lean_reconstruct` suites beyond the 17 kernel
suites + `real_lean_wire_differential`) — killed after ~25 minutes once the
kernel-specific numbers ADR-1600 needed were in hand, to free the shared
host; that broader scope is outside this lane's brief. `just check` /
`./scripts/check.sh` in full: not run (out of scope for a
docs-plus-one-script lane; the specific steps this lane added were verified
directly instead).

<!-- plan-section: landed-changes -->

| 2026-09-04 | metatheory-and-landmarks | `90940d7bb` ADR-1600: kernel trusted-core size (5,526 lines, re-derived), what it admits, four mutation-tested guards (3 clean, 1 found redundant), a fresh full `check-lean-gate.sh` run reproducing the known-red `max-to-imax` mutant, and what a relative soundness proof would require |
| 2026-09-04 | metatheory-and-landmarks | `adc3eda38` `scripts/count-landmark-facts.py` + baseline + `scripts/tests/test_count_landmark_facts.py` (9 guards) + `check.sh`/`justfile` registration: 1,432 landmark facts of 2,487 proved (57.6%) |
