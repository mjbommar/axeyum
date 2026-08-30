# Lane 152: sweep `scripts/tests/` for tests that restate their subject

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, 152-restate-sweep, 2026-08-27).** See the detail below.

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

Detail moved to [`../notes/152-restate-sweep.md`](../notes/152-restate-sweep.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | 152-restate-sweep | see this lane's detail above |
