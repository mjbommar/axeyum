# Notes: 279-gate-rot-triage

Detail moved out of [`../status/279-gate-rot-triage.md`](../status/279-gate-rot-triage.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Fix:** parsed the checker's own `DEPENDS_DERIVED_ERROR` output (never
transcribed by hand) and patched each fact's `depends_on` array as a
**surgical text substitution**, not a `json.dump` re-serialize — this
ledger's files are not uniformly formatted (`depends_on`/`free_symbols`
sometimes one-line compact, sometimes one-per-line), and a blanket re-dump
reformats unrelated fields. First attempt did exactly that and was reverted
before committing (`git checkout -- artifacts/facts/`) once the diff showed
unrelated `free_symbols` reflow. The surgical patcher round-trips through
JSON and asserts every non-`depends_on` field is byte-identical (checked
key-by-key across all 306 files: 0 violations) before writing.

`python3 scripts/check-fact-depends-derived.py --quiet`: exit 0,
`missing_edges=0` (was 1054). Commit `237c1abdd`.

## 2. Premise-selection proved-prefix control — STALE FIXTURE, guard is sound

`test_live_progress_must_be_a_proved_prefix` force-set the LAST
`bottom_up_chain` fact to `proved`, expecting a violation against the other
three (implicitly assumed `open`). All four are now genuinely `proved` in
the live ledger — the whole preregistered chain
(`F:ml430-nat-fib-add-two-b86e0c82` →
`F:ml430-nat-fib-coprime-fib-succ-162fc738` →
`F:ml430-nat-gcd-fib-add-self-5a92d5e3` → `F:ml430-nat-fib-gcd-d1d98407`) has
actually been proved since this policy was preregistered. So the old
mutation became a no-op against reality: forcing an already-`proved` fact to
`proved` again leaves all four `proved`, which trivially satisfies "forms a
proved prefix" instead of violating it.

**Verified this was the fixture, not the guard**, per the standing "a
checker that cannot fail is worse than none" rule: in a `copytree`d scratch
copy (never the tracked source, per the multi-agent hygiene rules), swapped
in a fixture that regresses an EARLIER chain fact
(`F:ml430-nat-gcd-fib-add-self-5a92d5e3`) to `open` while a LATER one stays
`proved` — a genuine gap regardless of how far real progress has advanced —
then deleted the guard (`first_open`/`any(... != "open" ...)` in
`validate_policy`) and confirmed **exactly one** test died (all other 7
stayed green). Restored the guard with the corrected fixture: all 8 pass.
Cleared `__pycache__` between iterations.

Applied the corrected fixture to the real test file.
`python3 -m unittest scripts.tests.test_check_autogenesis_nat_fib_gcd_premise_selection_policy`:
8 tests, OK (was 1 failure). Commit `166e789d1`.

## 3. `check-control-tests-reachable.py` — the interesting one

First pass measured the real orphan count at **9** against a committed
`ORPHAN_BASELINE` of 14 — reads as an improvement, and the test's own
docstring says to lower the baseline when the count falls. **Doing that
would have been wrong**, and only checking *why* the count moved caught it.

`scripts/control-optout.tsv` (ADR-0612, landed the same day) is
`name<TAB>reason`, not a script — its rows never start with `#`, and the
reason column routinely reads `pytest dialect; \`pytest\` is not installed`.
The scanner's existing comment guard (`ACommentIsAMentionHoweverRunnerishItLooks`,
added earlier for exactly this failure shape in `check-adopted-controls.sh`'s
`#`-comments) only skips lines starting with `#`, so it never saw this
format: **all seven of that file's `pytest dialect` rows were being credited
as "executed by scripts/control-optout.tsv"** — an exclusion ledger vouching
for the exact modules it names as unrun. Confirmed directly:
`CT.executed(...)` mapped each of `test_capture_maestro_device_id`
(+`_v2`/`_v3`), `test_diagnose_maestro_llvm_root_drift`,
`test_qf_linear_a5_census`, `test_qf_nia_a3_census`, `test_qf_uflia_a4_census`
to `{'scripts/control-optout.tsv'}` and nothing else.

**Fix:** excluded `scripts/control-optout.tsv` from `tracked()` outright
(`RUNNER_MENTION_TRAP`) — the same treatment `scripts/tests/` already gets,
for the identical reason: an exclusion registry documents non-coverage, it
cannot BE coverage. With the bug fixed, the seven reappear as real orphans,
joined by two genuinely new ones from ADR-0612's own glob-based
auto-discovery (`test_run_python_controls`, `test_frontier_definition_coverage`)
— both are actually run, every time, by `scripts/run-python-controls.py`,
but leave no literal `unittest`/`pytest` invocation line for this
text-scanning gate to see. **True count: 16**, not the naive 9 and not the
stale 14.

Raised `ORPHAN_BASELINE` 14 → 16 — a corrected measurement, not new rot; the
true count was always at least this high, hidden by the bug. Documented the
mechanism in the module docstring so the next recount doesn't rediscover it.
Added `AnOptoutReasonColumnIsNotARunnerLine` (3 tests: a synthetic pin
proving a bare optout-shaped row still fools the raw scanner, plus two
checks against the real tree). Verified non-vacuous in a **detached
worktree** (not the shared checkout, since mutating a tracked source
in-place breaks sibling lanes mid-build): reverting just the
`RUNNER_MENTION_TRAP` filtering kills exactly the 3 dependent tests, the
other 17 stay green.

`python3 -m unittest scripts.tests.test_check_control_tests_reachable`: 20
tests, OK (was 17, 1 failure). `python3 scripts/check-control-tests-reachable.py`:
exit 0, `orphaned=16|baseline=16` (was `orphaned=9|baseline=14`, passing
only because of the bug above). Commit `2bd5d391c`.

## Also run, foreground, as required

- `python3 scripts/validate-facts.py`: 1954 facts, 0 errors.
- `python3 scripts/gen-plan.py --check`: exit 0.

## What I did NOT touch

`artifacts/kernel-stack-envelope.tsv` (sibling lane's stack-envelope gates)
and the dependency-cycle gate (another lane's). Did not run the full
aggregate gate (`scripts/check.sh`), per instructions — the coordinator was
already running it.

## Commits (this branch, oldest first)

- `237c1abdd` — fix(ledger): re-derive 1054 missing depends_on edges across 306 facts
- `166e789d1` — fix(test): repair a stale fixture in the premise-selection proved-prefix control
- `2bd5d391c` — fix(gate): control-tests-reachable had a false-credit blind spot, not a stale baseline
