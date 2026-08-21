# Notes: local-ci-freshness

Detail behind [`../status/104-local-ci-freshness.md`](../status/104-local-ci-freshness.md).

## What "fresh" means, decided

- **Ancestor, not string/prefix match.** A record's `sha` must be HEAD or
  resolve via `git merge-base --is-ancestor <sha> HEAD`. A record for a sha
  NOT in HEAD's history (rebased away, or an unrelated line of history) is
  not "old" — it is inapplicable, and is reported/excluded distinctly from a
  merely-stale one.
- **"Newest" = fewest commits behind HEAD** among applicable records, not
  latest `finished_utc`. Re-running the gate today against a week-old sha
  would otherwise "refresh" a record's timestamp without the tested code
  moving any closer to HEAD.
- **Staleness budget is TIME (48h default,
  `AXEYUM_LOCAL_CI_FRESHNESS_MAX_AGE_HOURS`), not a commit count.** Measured on
  this branch: 171 commits in the 24h before this line was written, 53
  commits in the 5.6h between the one completed local-ci run and this
  checker, several concurrently-committing lanes — 7-10 commits/hour in
  bursts. A fixed commit-count ceiling has to be recalibrated against a
  velocity that swings that much; picked against today's rate it is either
  too strict the next time several lanes land a burst of docs/plan commits
  (reds the gate over changes the sweep never exercises) or too loose on a
  quiet weekend (a genuinely stale record reads as fresh because nothing else
  landed). What the checker protects against — main silently broken for a
  long stretch with nobody re-running the expensive gate — is a wall-clock
  exposure question. 48h is set against the run's own measured cost: ~107 min
  compute (`a6ee37c6a-s4.json`) serialized behind ONE lock across every lane
  on the box (`local-ci.sh`'s "one heavy cargo job at a time" rule, lock-wait
  budget up to 3h). Sub-day thresholds would be red by construction under
  that contention; a week would let a broken main hide through days of landed
  work.
- **The record's own `steps[]` decide pass/fail, never the top-level
  `verdict` field.** Every step must read `verdict == "pass"`; any `fail`,
  `vacuous`, or `unreadable` step reds the gate BY NAME regardless of what
  `verdict` claims, and a mismatch between the two (top says PASS with a bad
  step, or top says FAIL with all-pass steps) is its own reported reason. This
  is the "don't trust the summary field" pattern CLAUDE.md asks for
  everywhere else in this repo (`evidence_checked`, the axiom-count fields,
  `explain_corpus`).
- **No record at all, or no applicable record, is a FAILURE, not a report.**
  Absence is the limit case of staleness (infinitely old); treating it as
  merely informational recreates the exact "checker that exits 0 by default"
  defect this whole thread of work is about.

## Wiring decision: report-only, not enforcing

The only record that exists as of this commit
(`artifacts/local-ci-runs/a6ee37c6a-s4.json`) is `verdict: FAIL` — 4 nextest
failures, per 102-local-ci-run. Wiring this checker enforcing today would red
`just check` / `./scripts/check.sh` for every lane's every commit until
someone both fixes those 4 tests AND spends ~107 lock-serialized minutes
producing a fresh PASS record — a cost unrelated to almost any individual
change. That is precisely "a gate that is red from the day it lands is a gate
people learn to ignore" (this lane's own brief). Chose `--report-only`
(always exits 0, prints the identical verdict/reasons every run) over leaving
it unwired: the guard logic is exercised on every gate run either way, so the
moment a fresh all-pass record lands the printed line visibly flips from FAIL
to PASS, which is the trigger to delete `--report-only` from `scripts/check.sh`
and `justfile`'s `local-ci-freshness` recipe (one line each).

Confirmed against the real repo (2026-08-18, HEAD 53 commits ahead of
`a6ee37c6a`): the checker reports

```
local-ci-freshness: newest applicable record is '.../a6ee37c6a-s4.json' (sha=a6ee37c6a, 53 commit(s) behind HEAD, 1h old)
local-ci-freshness: FAIL
  - STEP FAILED: `cargo nextest run --profile local --workspace --all-features --no-fail-fast`
  - NON-PASS: record's top-level verdict is 'FAIL'
```

i.e. it is fresh in time and ancestor-valid, and reds purely on the actual
nextest failures — exactly the case this checker exists to catch.

## Demonstrated scenarios (`scripts/tests/test-check-local-ci-freshness.sh`)

Black-box: the control suite runs the REAL shipped script against a
disposable throwaway git repo (`AXEYUM_LOCAL_CI_FRESHNESS_REPO` /
`AXEYUM_LOCAL_CI_RECORDS` override the repo root and record dir), one
scenario at a time:

| case | fixture | want rc | reason text |
|---|---|---|---|
| no-record | empty record dir | 1 | `NO_RECORD` |
| stale | HEAD sha, `finished_utc` 100h ago | 1 | `STALE` |
| fail-step | top=PASS, one step `verdict:"fail"` | 1 | `` STEP FAILED: `...` `` |
| vacuous-step | top=PASS, one step `verdict:"vacuous"` | 1 | `` STEP VACUOUS: `...` `` |
| unreadable-step | top=PASS, one step `verdict:"unreadable"` | 1 | `` STEP UNREADABLE: `...` `` |
| non-ancestor | record for a divergent sidebranch sha | 1 | `NO_APPLICABLE_RECORD` |
| inconsistent-record | top=FAIL, all steps pass | 1 | `INCONSISTENT RECORD` |
| clean-pass | top=PASS, all steps pass, fresh | 0 | `local-ci-freshness: PASS` |
| report-only-still-diagnoses | stale AND fail-step, `--report-only` | 0 | `local-ci-freshness: FAIL` printed anyway |

All 9 pass on the shipped script (`bash scripts/tests/test-check-local-ci-freshness.sh`
→ `LOCAL_CI_FRESHNESS_CONTROLS|ok`).

## Mutation testing — every guard, done by hand this session

Copied the script to `/tmp/fresh.orig`, deleted one guard at a time with a
Python string-replace, ran the full control suite, recorded which case(s)
died, restored from the copy, moved to the next guard. No automated
mutation-testing harness was built — this was a one-time, by-hand pass,
documented here so the next lane can repeat it after any edit to the guard
logic.

| guard deleted | controls killed | count |
|---|---|---|
| G1 `NO_RECORD` → `fail=1` | `no-record` | 1 |
| G2 `NO_APPLICABLE_RECORD` → `fail=1` | `non-ancestor` | 1 |
| G3 in-loop ancestor check (`merge-base --is-ancestor`) | `non-ancestor` | 1 |
| G4 `STALE` → `fail=1` | `stale` | 1 |
| G5a step-loop `fail)` branch → `fail=1` | `fail-step` | 1 |
| G5b step-loop `vacuous)` branch → `fail=1` | `vacuous-step` | 1 |
| G5c step-loop `unreadable)` branch → `fail=1` | `unreadable-step` | 1 |
| G6 top-level-verdict `if` block | `inconsistent-record` | 1 |
| G7 `[ "$REPORT_ONLY" = 1 ] && exit 0` | `report-only-still-diagnoses` | 1 |

9 guards, 9 mutations, each kills **exactly one** control — no shared-check
pattern (the six-of-seven-guards failure mode CLAUDE.md measured elsewhere).

**One real near-miss, worth keeping:** the first draft of the
fail-step/vacuous-step/unreadable-step fixtures used a top-level `verdict:
"FAIL"` record. Deleting G5a (the fail-step guard) killed **zero** controls,
because the top-level-verdict guard (G6) independently set `fail=1` for the
same fixture — G6 was quietly doing G5's job. Fixed by changing those three
fixtures to top-level `verdict: "PASS"` with the bad step, which (a) actually
isolates the per-step guards from G6, and (b) is the more important scenario
substantively: a record honestly reporting FAIL is not dangerous, but one
FALSELY claiming PASS while hiding a failed/vacuous/unreadable step is
exactly the lie this checker exists to catch. Similarly, the report-only
control (case 9) was first built sharing the `fail-step`-only fixture with
case 3; deleting G5a would then have killed both. Fixed by giving case 9 a
compound fixture (stale AND fail-step) so it survives any single upstream
guard's deletion and only dies if the `--report-only` override itself breaks
— confirmed by mutating G7 alone.

## Left undone

- Flipping `--report-only` to enforcing in `scripts/check.sh` and `justfile`.
  Blocked on a fresh, ancestor, all-pass `local-ci --record` existing — not on
  this checker, which already reports the current (FAIL) state correctly.
- No CI/cron trigger for `scripts/local-ci.sh --record` itself — 102's own
  "left undone" (a timer on s5/s7, which as of 2026-08-18 cannot run the gate:
  no stable toolchain, no 1.88.0, no nextest, 342-422 commits behind).
- `--report-only`'s exit code is unconditionally 0 by design; a lane wanting a
  non-zero-but-non-blocking signal (e.g. for a dashboard) would need a third
  mode — not built, no current consumer needs it.

## Enforcing, 2026-08-19

One thing that is NOT a usable negative control:
`AXEYUM_LOCAL_CI_FRESHNESS_MAX_AGE_HOURS=0` does not red a minutes-old record,
because the guard compares integer hours with `-gt` and a fresh record is `0`.
Correct behaviour, useless as a probe — backdate `finished_utc` instead.

Flipping was re-tested through the real call site rather than the control suite,
since deleting a flag is exactly how a gate stops being able to fail: empty
record dir → `NO_RECORD`; `finished_utc` backdated five days → `STALE: 120h
exceeds 48h`; the nextest step rewritten `vacuous` → `STEP VACUOUS`; unmodified
→ `PASS`.
