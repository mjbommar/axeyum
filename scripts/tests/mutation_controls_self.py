"""The `mutation-controls` mutation table — the harness applied to itself.

This lives BESIDE `mutation_controls.py` rather than inside it for a mechanical
reason the harness itself reports: an anchor string stored in the file it
mutates occurs **twice** -- once as the guard, once as the table entry -- and
the harness refuses an anchor that matches in more than one place
(`AMBIGUOUS ANCHOR`), because `str.replace(..., 1)` would pick whichever came
first and say nothing about which.  Fifteen of these twenty-four anchors were in
exactly that state when they were written in one file, and the harness caught
every one.

Recursive on purpose.  The technique implemented next door is what every
"exactly one test died" in this repository rests on, and CLAUDE.md records six of
seven guards in one suite being removable with everything still green because
they all rejected through one shared check.  So each guard below is deleted and
must kill a control in `scripts/tests/test_mutation_controls.py`.
"""

from __future__ import annotations

SUBJECT = "scripts/tests/mutation_controls.py"
CONTROLS = "scripts.tests.test_mutation_controls"

MUTATIONS: list[tuple[str, ...]] = [
    # ---- classification: did the suite even run?
    ("no `Ran N` line is not a zero", "    if tests_run is None:", "    if False:"),
    ("zero tests is not a result", "    if tests_run == 0:", "    if False:"),
    (
        "a changed test count is not a result",
        "    if baseline_tests is not None and tests_run != baseline_tests:",
        "    if False:",
    ),
    # ---- classification: do the two independent kill counts agree?
    ("summary vs named deaths", "    if counted != len(deaths):", "    if False:"),
    (
        "a clean run must exit 0",
        "        if returncode != 0:\n            return Report(\n                INCONSISTENT,",
        "        if False:\n            return Report(\n                INCONSISTENT,",
    ),
    (
        "a run with deaths must exit nonzero",
        "    if returncode == 0:\n        return Report(\n            INCONSISTENT,",
        "    if False:\n        return Report(\n            INCONSISTENT,",
    ),
    (
        "an OK and a FAILED at once",
        "    if failed is not None and ok is not None:",
        "    if False:",
    ),
    (
        "no summary line to cross-check against",
        "    elif ok is not None:\n        counted = 0\n    else:",
        "    elif True:\n        counted = 0\n    else:",
    ),
    (
        "`errors=` counts as well as `failures=`",
        r'r"(failures|errors)=(\d+)"',
        r'r"(failures)=(\d+)"',
    ),
    # ---- classification: cargo, which is where the trap was found
    ("cargo lock timeout is not a verdict", "    if returncode == 75:", "    if False:"),
    (
        "a cargo binary that never reported",
        "    if len(blocks) != len(results):",
        "    if False:",
    ),
    (
        "cargo death names are parsed",
        r'r"^test (\S+) \.\.\. FAILED$"',
        r'r"^test (\S+) \.\.\. NEVERFAILED$"',
    ),
    # ---- did the mutation actually change anything?
    ("an absent anchor", "    if occurrences == 0:", "    if False:"),
    ("an anchor matching twice", "    if occurrences > 1:", "    if False:"),
    ("a replacement that is a no-op", "    if mutated == text:", "    if False:"),
    # ---- did the mutant build?
    (
        "the py_compile half of the build probe",
        "            if code != 0:\n                return (False, _tail(out))",
        "            if False:\n                return (False, _tail(out))",
    ),
    (
        "the import half of the build probe",
        '        code, out = _capture([sys.executable, "-c", f"import {self.module}"], work)\n        return (code == 0, _tail(out))',
        '        code, out = _capture([sys.executable, "-c", f"import {self.module}"], work)\n        return (True, _tail(out))',
    ),
    # ---- the driver
    (
        "a mutation may target a file other than the subject",
        "entry[3] if len(entry) > 3 else None",
        "None",
    ),
    (
        "the baseline must build",
        '        if not built:\n            print(f"{name}: BASELINE DID NOT BUILD; {why}")',
        '        if False:\n            print(f"{name}: BASELINE DID NOT BUILD; {why}")',
    ),
    ("the baseline must be green", "        if base.outcome != SURVIVED:", "        if False:"),
    (
        "the subject is restored between mutations",
        '    path.write_text(original, encoding="utf-8")\n    if path.read_text',
        "    if path.read_text",
    ),
    (
        "the restore is verified, not assumed",
        '    if path.read_text(encoding="utf-8") != original:',
        "    if False:",
    ),
    # ---- accounting: neither failure may be swallowed by the other
    (
        "an unmeasured mutation fails the run",
        "    if unmeasured:\n        status = 1",
        "    if unmeasured:\n        pass",
    ),
    (
        "a survivor fails the run",
        "    if survivors:\n        status = 1",
        "    if survivors:\n        pass",
    ),
]
