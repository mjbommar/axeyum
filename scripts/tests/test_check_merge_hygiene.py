#!/usr/bin/env python3
"""Controls for ``scripts/check-merge-hygiene.sh``.

CLAUDE.md: *a checker that cannot fail is worse than no checker.*  This gate
landed on 2026-08-30 with **zero** registered controls -- ``ls scripts/tests/ |
grep -c merge-hygiene`` returned 0 against a positive control of 1 -- so every
guard in it was a survivor by definition, whatever it did when run by hand.
The 2026-08-30 session audit named it first among five.

The shipped script is never re-implemented here.  ``AXEYUM_MERGE_HYGIENE_ROOT``
points the real file at a throwaway git repository whose ``scripts/gen-*.py``
are stubs, so each guard can be driven to failure and back without touching the
checkout.  Same device as ``AXEYUM_KERNEL_SUITES_ROOT``.

Every scenario drives ONE guard, plus the cases the gate must ACCEPT.  Deleting
a guard must kill at least one of these; registered with
``scripts/tests/mutation_controls.py`` under ``merge-hygiene``::

    python3 -m unittest scripts.tests.test_check_merge_hygiene
    python3 scripts/tests/mutation_controls.py merge-hygiene

**Conflict-marker text is BUILT, never written literally.**  This file is
scanned by the very guard it tests -- the exclusion was narrowed from
``scripts/tests/*`` to ``scripts/tests/fixtures/*`` in the same change -- so a
literal ``<<<<<<<`` here would make the gate fail on its own control suite.
``_marker()`` composes them from repeated characters instead, which is also the
only honest way to prove the narrowed exclusion is real.
"""

from __future__ import annotations

import os
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-merge-hygiene.sh"

# A generator stub: exits with $STUB_<NAME>_RC and prints a plausible line.
#
# `$STUB_<NAME>_OUT` appends a second line. It exists for exactly one guard:
# `check-shape-duplicates.py` exits 2 for TWO different reasons -- a malformed
# allowlist (a committed defect, must block) and an absent/stale prebuilt
# binary (a fact about this host, must not) -- and only the second prints a
# `SHAPE-DUPLICATES|UNAVAILABLE` marker. Without a way to vary the OUTPUT at a
# fixed rc there is no control for that split, and the gate could treat every 2
# as skippable with everything still green.
STUB = """#!/usr/bin/env python3
import os, sys
name = {name!r}
rc = int(os.environ.get("STUB_" + name + "_RC", "0"))
print(f"{{name}}: {tag} rc={{rc}}")
extra = os.environ.get("STUB_" + name + "_OUT", "")
if extra:
    print(extra)
sys.exit(rc)
"""


def _marker(char: str, suffix: str = "") -> str:
    """A conflict marker built at runtime -- see the module docstring."""
    return char * 7 + suffix


def _ctx(done: subprocess.CompletedProcess) -> str:
    """The gate's output as an assertion message, INDENTED so no line starts
    with ``FAIL:``.

    Found 2026-09-02 registering the shape-duplicates guard.
    ``mutation_controls.py`` names the tests a mutant killed with
    ``^(?:FAIL|ERROR): (\\S+)`` over unittest's output, and cross-checks that
    count against ``FAILED (failures=N)``. The gate under test prints its own
    findings as ``FAIL: <check>`` at line start -- the convention every check
    in it follows -- so a raw ``done.stdout`` in a failing assertion's message
    is parsed as a SECOND dead test, and the harness reports ``INCONSISTENT --
    the summary line says 1 died but 2 were named`` for a mutant that in fact
    killed exactly one.

    That is the harness behaving correctly: it refuses to report a number it
    cannot cross-check, which is the whole point of it. Nothing before this
    tripped it, because no earlier mutant made a test fail while capturing gate
    output that contained a ``FAIL:`` line. Indenting costs nothing and keeps
    the full context in the message.
    """
    return "\n" + "".join(f"  {line}\n" for line in (done.stdout + done.stderr).splitlines())


class MergeHygieneControls(unittest.TestCase):
    """One scenario per guard in `scripts/check-merge-hygiene.sh`."""

    def setUp(self) -> None:
        scratch = pathlib.Path("/data0/axeyum/scratch")
        self._tmp = tempfile.TemporaryDirectory(dir=scratch if scratch.is_dir() else None)
        self.addCleanup(self._tmp.cleanup)
        self.root = pathlib.Path(self._tmp.name) / "tree"
        (self.root / "scripts").mkdir(parents=True)
        self.git("init", "-q")
        self.git("config", "user.email", "t@example.com")
        self.git("config", "user.name", "t")
        for name, tag in (
            ("gen-adr-index", "ADR_INDEX ok"),
            ("gen-plan", "plan ok"),
            # ADR-1511: the two cheap ledger checks the gate now runs for real.
            ("gen-import-backlog", "IMPORT_BACKLOG ok"),
            ("gen-production-provenance-ledger", "PRODUCTION_PROVENANCE ok"),
            # The creal STEPS table is a GENERATED SOURCE FILE, checked here
            # for the same reason PLAN.md is (lane `creal-split-2`).
            ("creal-declare-deps", "CREAL_DECLARE_DEPS ok"),
            # The Python binding's prelude field table -- the generated file
            # that reached main stale because its `--check` was in no gate.
            ("gen-py-prelude-fields", "PRELUDE-FIELDS ok"),
            # The census guard (lane `shape-census`): stubbed like the generators so
            # the scenario chooses the exit and the THREE-outcome dispatch is measured.
            ("frontier-shape-census", "SHAPE_CENSUS ok"),
            # The duplicate-declaration gate, given a no-cargo route so it can
            # run here at all (ADR-1511 amendment 2026-09-02). It was red on
            # main for ~25 hours in 0 of 240 commit messages because its only
            # route was `cargo run --release`.
            ("check-shape-duplicates", "OK: 10 duplicate group(s) (route: prebuilt)"),
        ):
            path = self.root / "scripts" / f"{name}.py"
            path.write_text(STUB.format(name=name.replace("-", "_").upper(), tag=tag))
        self.write("README.md", "clean\n")
        self.git("commit", "-qm", "base")

    # -- tree construction --------------------------------------------------

    def _git_env(self) -> dict[str, str]:
        # A lane exports GIT_INDEX_FILE (CLAUDE.md's per-process index remedy)
        # and it points at the REAL checkout's private index. Inherited here it
        # would make every `git add` in this scratch repo write there instead.
        env = dict(os.environ)
        for var in ("GIT_INDEX_FILE", "GIT_DIR", "GIT_WORK_TREE", "GIT_CONFIG"):
            env.pop(var, None)
        return env

    def git(self, *args: str) -> None:
        subprocess.run(("git", *args), cwd=self.root, check=True, env=self._git_env(),
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    def write(self, rel: str, text: str, *, track: bool = True) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        if track:
            self.git("add", "-A")

    def run_gate(self, _stub_out: dict[str, str] | None = None, **stub_rc: int
                 ) -> subprocess.CompletedProcess:
        env = self._git_env()
        env["AXEYUM_MERGE_HYGIENE_ROOT"] = str(self.root)
        for name, rc in stub_rc.items():
            env[f"STUB_{name.upper()}_RC"] = str(rc)
        for name, text in (_stub_out or {}).items():
            env[f"STUB_{name.upper()}_OUT"] = text
        return subprocess.run(
            ["bash", str(SCRIPT)], cwd=ROOT, env=env,
            capture_output=True, text=True, timeout=120,
        )

    # -- the accept case ----------------------------------------------------

    def test_clean_tree_passes_and_prints_its_summary(self) -> None:
        """The positive control. Without it every guard below is satisfiable
        by a gate that always fails, which is not a gate either."""
        done = self.run_gate()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("MERGE_HYGIENE|markers=0", done.stdout)
        self.assertIn("|PASS", done.stdout)

    # -- guard 1: conflict markers ------------------------------------------

    def test_conflict_marker_in_a_tracked_rust_file_fails(self) -> None:
        self.write("src/lib.rs", f"fn a() {{}}\n{_marker('<', ' ours')}\nfn b() {{}}\n")
        done = self.run_gate()
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("conflict markers", done.stdout)
        self.assertIn("src/lib.rs", done.stdout)

    def test_a_bare_seven_equals_line_is_a_marker(self) -> None:
        """The middle marker carries no trailing text, so a pattern written
        only for `        often in a JSON fact file."""
        self.write("artifacts/facts/F-x.json", "{\n" + _marker("=") + "\n}\n")
        done = self.run_gate()
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("artifacts/facts/F-x.json", done.stdout)

    def test_a_marker_in_a_control_suite_is_NOT_exempt(self) -> None:
        """The narrowed exclusion. `scripts/tests/*` was excluded wholesale,
        which exempted every control suite in the repository from the gate
        whose controls those are."""
        self.write("scripts/tests/test-thing.sh", f"#!/bin/sh\n{_marker('>', ' theirs')}\n")
        done = self.run_gate()
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("scripts/tests/test-thing.sh", done.stdout)

    def test_a_marker_under_tests_fixtures_IS_exempt(self) -> None:
        """The other side of the same narrowing: fixture data is allowed to
        contain marker text, and the gate must still pass."""
        self.write("scripts/tests/fixtures/conflicted.txt", _marker("<", " ours") + "\n")
        done = self.run_gate()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("markers=0", done.stdout)

    def test_an_untracked_file_with_markers_does_not_fail_the_gate(self) -> None:
        """`git grep` scans the index, deliberately: a lane's untracked scratch
        file is not a merge defect and must not make the gate red for everyone."""
        self.write("scratch.txt", _marker("<", " ours") + "\n", track=False)
        done = self.run_gate()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)

    # -- guard 5/6 (ADR-1511): the cheap ledger checks block ----------------

    def test_import_backlog_check_failure_fails_the_gate(self) -> None:
        """Deleting the `gen-import-backlog.py --check` guard must kill exactly
        this test. Measured 2026-09-01: the generator was red on main for a day
        (147 -> 164 rows) and nothing at merge time said so."""
        done = self.run_gate(gen_import_backlog=1)
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("FAIL: gen-import-backlog.py --check", done.stdout)

    def test_production_provenance_check_failure_fails_the_gate(self) -> None:
        """Same shape for the provenance ledger, which `--check` reported stale
        (2,054 published vs 2,343 live) while every merge went through."""
        done = self.run_gate(gen_production_provenance_ledger=1)
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("FAIL: gen-production-provenance-ledger.py --check", done.stdout)

    # -- guard 2: duplicate ADR numbers -------------------------------------

    def test_adr_index_check_failure_fails_the_gate(self) -> None:
        done = self.run_gate(gen_adr_index=1)
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("FAIL: gen-adr-index.py --check", done.stdout)
        self.assertIn("Renumber the NEWER one", done.stdout)

    def test_adr_index_failure_output_is_reported_not_swallowed(self) -> None:
        """The remedy is useless without the ADR_INDEX line naming the clash;
        the gate captures the checker's own output with 2>&1 for this."""
        done = self.run_gate(gen_adr_index=1)
        self.assertIn("ADR_INDEX", done.stdout)

    # -- guard 3: stale generated files -------------------------------------

    def test_stale_plan_fails_the_gate(self) -> None:
        done = self.run_gate(gen_plan=1)
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("FAIL: gen-plan.py --check", done.stdout)
        self.assertIn("commit PLAN.md", done.stdout)

    def test_stale_creal_steps_table_fails_the_gate(self) -> None:
        """`crates/.../creal/steps_generated.rs` is the `STEPS` array the creal
        prelude builds against and it is generated from a measurement of
        `creal.rs`. A stale one silently under-constrains the build order --
        which is the defect the generator replaced -- and `creal.rs` has the
        highest edit rate in the repository, so it is the generated file most
        likely to be merged stale."""
        done = self.run_gate(creal_declare_deps=1)
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("FAIL: creal-declare-deps.py --check", done.stdout)
        self.assertIn("steps_generated.rs", done.stdout)

    # -- guard 8: the Python prelude field table ---------------------------

    def test_stale_python_prelude_field_table_fails_the_gate(self) -> None:
        """`crates/axeyum-py/src/kernel/prelude_fields.rs` names every prelude
        field for the Python binding. When ADR-1512 moved 69 `CRealPrelude`
        names behind per-module registries, the regeneration that unbroke main
        deleted all 69 from the binding and no gate noticed -- because
        `gen-py-prelude-fields.py --check` was registered in none. A missing
        field reads as `that theorem does not exist`."""
        done = self.run_gate(gen_py_prelude_fields=1)
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("FAIL: gen-py-prelude-fields.py --check", done.stdout)
        self.assertIn("prelude_fields.rs", done.stdout)

    def test_missing_rustfmt_is_reported_as_skipped_not_as_stale(self) -> None:
        """Exit 2 is the generator's `cannot answer`: the committed file is
        `rustfmt`'s fixed point, so without `rustfmt` every tree compares as
        drifted. Measured 2026-08-16, `just` and `lean` were present on one
        fleet host of five -- a gate that assumes a toolchain manufactures a red
        that means nothing. This is the control that a rc=2 does NOT fail the
        gate and IS named in the output."""
        done = self.run_gate(gen_py_prelude_fields=2)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("SKIPPED (rustfmt not on PATH)", done.stdout)
        self.assertIn("py_prelude_fields=skipped (no rustfmt)", done.stdout)
    # -- guard 4: the frontier shape census ---------------------------------

    def test_stale_shape_census_fails_the_gate(self) -> None:
        done = self.run_gate(frontier_shape_census=1)
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("FAIL: frontier-shape-census.py --check", done.stdout)
        self.assertIn("frontier-shape-census-v1.json", done.stdout)

    def test_an_unanswerable_shape_census_does_NOT_fail_the_gate(self) -> None:
        """Exit 2 is the census saying it could not compute an answer. A gate
        that reports a disagreement when its subject was unavailable is wrong
        about its own subject -- so 2 is reported, not failed."""
        done = self.run_gate(frontier_shape_census=2)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("shape_census=not-answerable", done.stdout)
        self.assertIn("|PASS", done.stdout)

    # -- guard 7 (ADR-1511 amendment): duplicate declarations ---------------

    def test_a_reported_duplicate_group_fails_the_gate(self) -> None:
        """Deleting the shape-duplicates guard must kill exactly this test.

        This is the check CLAUDE.md calls the binding cost gate: two
        declarations proving one proposition is what a lane produces when it
        cannot find an existing lemma. It was red on `main` for ~25 hours and
        named in 0 of that day's 240 commit messages, and a literal duplicate
        landed 16 hours after its twin inside the window -- because its only
        route was a release cargo build, so it lived only in the ~10-minute
        gate (lane `retrieval-audit-0901`)."""
        done = self.run_gate(check_shape_duplicates=1)
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("FAIL: check-shape-duplicates.py --prebuilt", done.stdout)
        self.assertIn("shape-duplicates-allowlist.json", done.stdout)

    def test_an_absent_or_stale_prebuilt_binary_is_skipped_not_failed(self) -> None:
        """Exit 2 WITH the marker is `cannot answer`, and must not block.

        A prebuilt binary that was never built here, or that predates a kernel
        source, indexes an OLD environment -- so it would report a duplicate
        that landed after the build as ABSENT. Answering from it is worse than
        not answering, and turning a missing `target/` red is noise that
        teaches a coordinator to ignore the gate."""
        done = self.run_gate(
            {"check_shape_duplicates": "SHAPE-DUPLICATES|UNAVAILABLE stale-binary -- older"},
            check_shape_duplicates=2,
        )
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertIn("SKIPPED (stale-binary)", done.stdout)
        self.assertIn("shape_duplicates=skipped(stale-binary)", done.stdout)

    def test_exit_two_WITHOUT_the_marker_still_fails_the_gate(self) -> None:
        """The other half of the split, and the one that is easy to lose.

        `check-shape-duplicates.py` also exits 2 for a MALFORMED ALLOWLIST --
        a defect in a committed file, pinned by that script's own
        `test_malformed_allowlist_exits_two`. A gate that read every 2 as
        `skipped` would swallow it, which is the checker-that-cannot-fail
        defect arriving through the door marked `be lenient about toolchains`.
        The marker, not the exit code, is what separates them."""
        done = self.run_gate(check_shape_duplicates=2)
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("FAIL: check-shape-duplicates.py --prebuilt (exit 2)", done.stdout)

    def test_the_shape_duplicates_check_can_be_opted_out(self) -> None:
        """The documented escape, defaulting ON. It must be reported in the
        summary rather than silently absent, so a run that did not check is
        distinguishable from one that checked and found nothing."""
        env_gate = self.run_gate(check_shape_duplicates=1)
        self.assertEqual(env_gate.returncode, 1, "control: the guard fires without the opt-out")
        os.environ["AXEYUM_SKIP_SHAPE_DUPLICATES"] = "1"
        self.addCleanup(os.environ.pop, "AXEYUM_SKIP_SHAPE_DUPLICATES", None)
        done = self.run_gate(check_shape_duplicates=1)
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertIn("AXEYUM_SKIP_SHAPE_DUPLICATES=1", done.stdout)

    # -- the aggregate ------------------------------------------------------

    def test_every_failure_is_reported_not_only_the_first(self) -> None:
        """A merge that broke two things must name both; short-circuiting after
        the first sends the coordinator back for a second round."""
        self.write("src/lib.rs", _marker("<", " ours") + "\n")
        done = self.run_gate(gen_adr_index=1, gen_plan=1)
        self.assertEqual(done.returncode, 1)
        self.assertIn("conflict markers", done.stdout)
        self.assertIn("gen-adr-index.py --check", done.stdout)
        self.assertIn("gen-plan.py --check", done.stdout)
        self.assertIn("MERGE_HYGIENE|FAILED", done.stdout)


if __name__ == "__main__":
    unittest.main()
