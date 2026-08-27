# Lane 152: sweep `scripts/tests/` for tests that restate their subject

## Status: COMPLETED — swept, no repair needed, one gate gap found

### Task

Find tests shaped like the `test-allowlist-fix.py` / `mutation-verify-guards.py`
defect fixed upstream on 2026-08-27 (commit `c116b1165`): a test that defines
its own copy of a subject's regex/constant/table and asserts against the copy
instead of loading `validate-facts.py` (or any other subject). Such a test
cannot fail when the subject changes — the checker-that-cannot-fail defect,
inside a test.

### Method

383 `scripts/tests/*.py` files, 19 `scripts/tests/*.sh` files. Three
independent, overlapping scans of the full `.py` corpus, cross-checked against
each other and against manual reading of every file any scan flagged:

1. **No-subject-load scan**: files matching neither `spec_from_file_location`,
   `sys.path.insert` + bare import, `from scripts import …`, nor a
   `subprocess.run/check_call/check_output/Popen(` call. 383 files scanned,
   1 hit: `mutation_controls_self.py` — not a test (no `unittest.TestCase`,
   no assertions); it is a mutation table consumed by
   `mutation_controls.py:1656` via `spec_from_file_location`, confirmed by
   grep. Not a defect.

2. **Constant-duplication scan**: files defining a module-level
   `UPPER_CASE = re.compile(...) / {...} / [...] / "..."` constant, cross-
   referenced against subject-loading patterns. 58 files define such a
   constant; 3 have no subject-loading pattern by the narrow first-pass
   regex. Two (`test_check_kernel_suites.py`, `test_check_reflection_semantics_gate.py`)
   were false positives of the regex — both load their subject via
   `subprocess.run(["bash"/sys.executable, str(SCRIPT_OR_CHECKER), ...])`
   against a synthetic tree; their module-level constants (`STUB_CARGO`,
   `BINARIES`, `PROBE`, `PLAIN`) are fixture inputs fed to the real subject,
   not restated subject logic. Read both files in full to confirm. Third hit
   was `mutation_controls_self.py` again.

3. **Subject-mention scan**: every `scripts/xxx.py`/`.sh` path named in a
   test file's docstring/comments, cross-checked for a load mechanism
   (subprocess, `spec_from_file_location`, `sys.path.insert` + import,
   `from scripts import`) *and*, separately, for tests that only
   `.read_text()`/`open()` a mentioned subject without ever executing/
   importing it (parses source text instead of running it — a milder variant
   of the same defect). 221 files mention a subject path; 0 have neither a
   load mechanism after accounting for `from scripts import X` package
   imports (the two `test_lean_execution_acceptance.py` /
   `test_lean_u2_official_execution.py` false positives from an earlier pass
   were `from scripts import lean_execution_acceptance as ACCEPTANCE` /
   `... lean_u2_official_execution as U2`, both genuine package imports).
   The read-only-text variant found only `mutation_controls_self.py` again.

All 19 `.sh` test files were read (each names its subject in a header
comment: `# Controls for scripts/X`) and confirmed to invoke the real subject
directly (`"$CS"`/`scripts/foo.sh`/`hooks/commit-msg`), not a restated copy.

### Result: no new defect found

**383 `.py` files and 19 `.sh` files examined; 0 carry the restate-the-subject
defect beyond the pair already fixed upstream.** No repair was made —
CLAUDE.md's own rule against weakening a test cuts the other way here: there
was nothing vacuous to strengthen, so nothing in `scripts/tests/` was
touched.

### Hyphenated test files: none remain

`test-allowlist-fix.py` and `mutation-verify-guards.py` (both hyphenated,
unimportable by name — exactly the shape CLAUDE.md's brief calls the
highest-yield place to look) are gone, replaced upstream by
`test_validate_facts_allowlist.py`. `ls scripts/tests/*.py | grep -E
'/[a-zA-Z0-9_]*-[a-zA-Z0-9_-]*\.py$'` (via `/usr/bin/grep`, not the
interactive `ugrep` shim) returns nothing. No other hyphenated `.py` test
file exists in the directory.

### Gate finding: `check-control-registration.sh` could not have caught this,
### structurally, and its Python ratchet is *already* red

Two separate points, not one:

1. **Registration and vacuity are orthogonal properties.**
   `check-control-registration.sh` answers "is this file named by
   `scripts/check.sh`, the `justfile`, `hooks/pre-push`, or
   `.github/workflows`" — i.e. does *something* run it. It says nothing about
   whether the test can fail. A test that restates its subject can be
   perfectly registered, run on every push, and still never catch a
   regression, because its assertions never touch the subject. The two
   original defective files could have been wired into `check.sh` verbatim
   and this gate would have reported them green.

2. **Independent of point 1, its Python-suite glob is structurally blind to
   hyphenated names.** The loop is `for f in scripts/tests/test_*.py` —
   requires a literal underscore right after `test`. Verified by dropping a
   throwaway `scripts/tests/test-scratch-hyphen-probe.py` into the directory
   (untracked, removed immediately after): `py_controls` did not count it at
   all. The `.sh` half's glob (`scripts/tests/*.sh`) has no such restriction
   and would have counted a hyphenated `.sh` control — but the two original
   defective files were `.py`. So a hyphenated-and-unregistered-and-vacuous
   `.py` test is invisible to this gate on *two* independent axes: it
   measures the wrong property (registration, not correctness), and even for
   the property it does measure, hyphenated `.py` files fall outside its
   glob.

3. **The ratchet is currently ROSE, right now, in this tree**, unrelated to
   anything this lane touched:

       CONTROL_REGISTRATION|controls=19|orphans=0|py_controls=381|py_orphans=191|py_baseline=188|py=ROSE

   `test_validate_facts_allowlist.py` — the file this lane's brief names as
   *"your model for what a repaired test looks like"* — is itself one of the
   191 unregistered suites: `grep -rF "test_validate_facts_allowlist"
   scripts/check.sh justfile hooks/pre-push` returns nothing, exit 1. This is
   a pre-existing gate state from the merge, not something this lane
   introduced (nothing in `scripts/tests/` was edited), and it is out of this
   lane's scope to fix (`scripts/check.sh`/`justfile` are not
   `scripts/tests/`). Reporting it rather than fixing it, per the brief's
   instruction to report an out-of-scope subject problem and stop.

### Verification

- `python3 scripts/validate-facts.py` — green: `1815 facts checked, 0
  errors`.
- `python3 -m unittest scripts.tests.test_validate_facts_allowlist -v` — 6/6
  pass (confirms the merged model file still works standalone).
- No files under `scripts/tests/` were modified; nothing to re-verify by
  mutation.
