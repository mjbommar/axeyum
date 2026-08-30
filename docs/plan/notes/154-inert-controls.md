# Notes: 154-inert-controls

Detail moved out of [`../status/154-inert-controls.md`](../status/154-inert-controls.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **10 were pytest-dialect** — bare module-level `def test_x()`, no `TestCase`.
  `python3 -m unittest` collects **nothing** from these. Registering one without
  a zero-test guard would have added a step that cannot fail.
  **9 of the 10 pass when their functions are actually executed**, so they were
  wrapped in a `TestCase` (nothing any of them asserts was changed) and now
  contribute **20 real tests where 0 ran before**. The tenth needs pytest's
  `tmp_path` fixture and has a genuinely failing assertion.
- **6 `import pytest`, and pytest is installed on no host in this fleet.** They
  use it only for `pytest.raises(E, match=…)`, which is `assertRaisesRegex` in
  the dialect everything else here uses — a mechanical rewrite, not done in this
  lane because converting a suite changes what it asserts and these guard
  capture/census producers owned elsewhere.

**12 more are RED on `main`.** These are drift detectors that have been firing
into an empty room:

- `test_prove_tock_log2{,_v2,_v3,_v4}` — `registration/producer_files_hash`
  mismatch for `crates/axeyum-verify/tests/tock_log2_external.rs`. The file
  exists; its content no longer matches the recorded digest. Content-hash, so
  path-independent — not a worktree artefact.
- `test_validate_glaurung_llvm_loop_semantic_census` — `producer drift: Cargo.lock`.
- `test_check_autogenesis_official_gcd_balanced_bezout_{generic_base,official_kernel}_result`
  — `implementation identity changed`.
- Four assert error strings their checkers no longer emit (`budget`,
  `boundary`, `dependency`, `comparison differs`).
- `test_check_autogenesis_balanced_bezout_euclidean_update_dependency_audit_plan`
  needs `target/debug/examples/theorem_footprint_batch_audit`, which no fast
  gate builds.

None of that is fixable from this lane — `artifacts/` and `crates/` are other
lanes' scope — so all 19 are **named** in `scripts/control-optout.tsv` with the
error each one produces. They are liabilities, not settlements.

## The structural change

`scripts/run-python-controls.py` (new). Discovers every
`scripts/tests/test_*.py`, subtracts the suites a caller already names and the
reasoned exclusions, runs the rest in parallel. It is a **catch-all**, so a
suite that gets its own `step` later is dropped from it automatically and
nothing is maintained in two places. Registered in both `scripts/check.sh` and
the `justfile`. Full decision and the rejected alternatives:
[ADR-0612](../../research/09-decisions/adr-0612-control-registration-is-derived-not-remembered.md).

`scripts/control-optout.tsv` (new) replaces `PY_ORPHAN_BASELINE=188`. Format is
`name<TAB>reason`; missing reason, missing TAB, duplicate, or an entry naming a
file that no longer exists are all errors. **Fails in both directions**, the
shape `check-shape-duplicates.py` and `check-absence-claims.py` already use.

`scripts/check-control-registration.sh`'s Python half was rewritten around seven
guards. Why the floor is not simply lowered: after this change nothing *can* be
an orphan, so "how many are unnamed" is no longer a question worth ratcheting.
What is worth checking is that the construction is intact.

## The baseline reduction, and why each part was earned

**`py_orphans` 188 → 0.** Not absorbed:

- **169 → run.** They execute, in the aggregate gate, every time. 1,193 tests.
- **+1** — this lane's own `test_run_python_controls`, discovered by the runner
  it tests. No registration step; that is the demonstration.
- **19 → named with a written reason**, each carrying the error it produces.
- **0 → deleted.** Nothing was obsolete.

The remaining pin is `OPTOUT_CEILING=19`, over a list a reviewer can read.

## Hyphenated names: forbidden, not accommodated

The gate's `test_*.py` glob is blind to `test-foo.py` (confirmed by probe), and
`python3 -m unittest scripts.tests.test-foo` cannot run it either — a hyphenated
name is not an importable module. Teaching the glob to see them would fix half
the problem and leave the file unrunnable. **G2 rejects any hyphenated `.py`
under `scripts/tests/`.** `.sh` controls keep hyphens: they are invoked by path,
and all 21 are registered.

## Mutation evidence

Copies mutated in scratch, never the shared tree; `__pycache__` cleared and
`-B` used between Python mutants (equal-size mutants otherwise report the
*previous* result); every replacement asserted to have applied, with a loud SKIP
otherwise.

`scripts/check-control-registration.sh` — **12/12 killed**: G1 runner-invoked
(→ `runner-not-invoked`, `runner-named-only-in-a-comment`), G2 hyphenated-py,
G3 optout-stale, G4 optout-reason, G4b optout-tab, G5 optout-and-named,
G6a optout-rose, G6b optout-fell, G7 partition-agree, `.sh` orphans,
`.sh` corpus floor, optout-file-present.

`scripts/run-python-controls.py` — **12/12 killed**: R1 no-TAB, R2 reason,
R3 duplicate, R4 file-present, R5 corpus floor, R6 stale entry,
R7 comments-are-not-callers, R8 both-invocation-forms, R9 red-on-failure,
R10 zero-test detection, R11 total-tests floor, R12 optout-is-subtracted.
**R11 SURVIVED the first round** — nothing killed it, so it was decoration until
`test_a_corpus_that_collects_almost_nothing_hits_the_test_floor` was written for
it. Recorded because a guard that survives is the finding.

## Two pre-existing reds found while verifying, neither caused here

- **`scripts/check-shell-antipatterns.sh` exits 1 on `main`**: `render/check.sh`
  (from `a69ebd4bc`) and `scripts/tests/test-lane-commit.sh` each use `grep -q`
  in a pipeline under `pipefail` and are absent from
  `scripts/check-shell-antipatterns.baseline`. Neither file nor the baseline was
  touched here.
- **`scripts/check-aggregate-scope.sh` exits 1**: 12 unrecorded one-sided steps.
  Four were control suites landed that day in `scripts/check.sh` only —
  including two of the three orphans the deficiency doc names — so `just check`,
  the gate CLAUDE.md calls preferred, did not run them. Those four are now in
  the `justfile` too, **12 → 8**. The remaining 8 are `uv run` python-binding
  steps, out of this lane's scope.

## Left undone, deliberately

- The 6 pytest-importing suites are a mechanical `assertRaisesRegex` rewrite
  each; not done, because it changes what they assert.
- The 12 red suites need their owners: re-capture a digest, or update an
  expected error string.
- `hooks/pre-push` was not touched (out of scope). The catch-all is a 39 s
  Python step with no cargo lock, so adding it there is cheap if wanted.
