"""Controls for the mutation harness itself.

`scripts/tests/mutation_controls.py` is what makes every "exactly one test died"
in this repository mean anything, and until 2026-08-18 it could not tell a
mutant that **failed to compile** from a guard that was genuinely unreachable:
both arrived as a non-zero exit with no dead tests, and both were scored as
coverage.  A checker that cannot fail is worse than no checker, so the harness
gets the same treatment it applies to everything else:

    python3 scripts/tests/mutation_controls.py mutation-controls

deletes its guards one at a time and requires each deletion to kill a test here.

Every control below drives **one** guard, from a fixture that trips that guard
and no other.  Where two guards would otherwise reject through the same shared
check -- CLAUDE.md records six of seven doing exactly that in one suite -- the
control asserts the *detail* string as well as the outcome, so the two are
distinguishable at the point where they are actually different.

The unit controls feed the classifiers raw runner output, so no build happens.
The three end-to-end controls copy the tree and are the slow ones (~1.3 s each);
they are what covers the driver, the build probe and the baseline refusal.
"""

from __future__ import annotations

import importlib.util
import io
import contextlib
import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "mutation_controls", ROOT / "scripts" / "tests" / "mutation_controls.py"
)
assert SPEC is not None and SPEC.loader is not None
MC = importlib.util.module_from_spec(SPEC)
sys.modules["mutation_controls"] = MC
SPEC.loader.exec_module(MC)


def unittest_output(ran: int | None, summary: str | None, deaths: tuple[str, ...] = ()) -> str:
    lines = [f"{name} (some.module.Case.{name})" for name in ()]
    for name in deaths:
        lines.append(f"FAIL: {name} (some.module.Case.{name})")
    if ran is not None:
        lines.append(f"Ran {ran} tests in 0.010s")
    lines.append("")
    if summary is not None:
        lines.append(summary)
    return "\n".join(lines) + "\n"


# --------------------------------------------------------------------- shape


class OutcomeShapeTests(unittest.TestCase):
    def test_only_killed_and_survived_are_measurements(self) -> None:
        self.assertEqual(set(MC.MEASUREMENTS), {MC.KILLED, MC.SURVIVED})
        for outcome in (MC.NO_BUILD, MC.NO_RUN, MC.NOT_APPLIED, MC.AMBIGUOUS, MC.INCONSISTENT):
            self.assertFalse(MC.Report(outcome).measured, outcome)


# ------------------------------------------------- classify_unittest guards


class UnittestClassifierTests(unittest.TestCase):
    def test_a_run_that_reported_no_count_is_not_a_result(self) -> None:
        """Guard: `tests_run is None`. No `Ran N` line at all -- the runner died."""
        report = MC.classify_unittest(1, "Traceback (most recent call last):\nboom\n", None)
        self.assertEqual(report.outcome, MC.NO_RUN)
        self.assertIn("never reported", report.detail)

    def test_zero_tests_is_not_a_result(self) -> None:
        """Guard: `tests_run == 0`. The `#![cfg(feature = "full")]` shape."""
        report = MC.classify_unittest(5, unittest_output(0, "NO TESTS RAN"), None)
        self.assertEqual(report.outcome, MC.NO_RUN)
        self.assertIn("zero tests", report.detail)

    def test_a_different_test_count_from_the_baseline_is_not_a_result(self) -> None:
        """Guard: collection changed under the mutation, so nothing is comparable."""
        report = MC.classify_unittest(0, unittest_output(5, "OK"), 7)
        self.assertEqual(report.outcome, MC.NO_RUN)
        self.assertIn("collection changed", report.detail)

    def test_disagreeing_kill_counts_are_refused(self) -> None:
        """Guard: the summary line and the FAIL:/ERROR: headers must agree."""
        report = MC.classify_unittest(
            1, unittest_output(4, "FAILED (failures=2)", ("test_one",)), 4
        )
        self.assertEqual(report.outcome, MC.INCONSISTENT)
        self.assertIn("but 1 were named", report.detail)

    def test_a_clean_run_that_exits_nonzero_is_refused(self) -> None:
        """Guard: exit status must agree with a clean summary."""
        report = MC.classify_unittest(3, unittest_output(4, "OK"), 4)
        self.assertEqual(report.outcome, MC.INCONSISTENT)
        self.assertIn("exit status is 3", report.detail)

    def test_a_dead_test_with_a_zero_exit_is_refused(self) -> None:
        """Guard: the other direction -- deaths reported, exit status says fine."""
        report = MC.classify_unittest(
            0, unittest_output(4, "FAILED (failures=1)", ("test_one",)), 4
        )
        self.assertEqual(report.outcome, MC.INCONSISTENT)
        self.assertIn("exit status is 0", report.detail)

    def test_both_summary_lines_at_once_is_refused(self) -> None:
        """Guard: an OK and a FAILED in one output means the output is not one run."""
        text = unittest_output(4, "FAILED (failures=1)", ("test_one",)) + "OK\n"
        report = MC.classify_unittest(1, text, 4)
        self.assertEqual(report.outcome, MC.INCONSISTENT)
        self.assertIn("both an OK and a FAILED", report.detail)

    def test_no_summary_line_at_all_is_refused(self) -> None:
        """Guard: without OK/FAILED there is no second count to cross-check."""
        report = MC.classify_unittest(1, unittest_output(3, None), 3)
        self.assertEqual(report.outcome, MC.INCONSISTENT)
        self.assertIn("no OK/FAILED summary", report.detail)

    def test_errors_count_toward_the_summary_as_well_as_failures(self) -> None:
        """Guard: the summary total sums `failures=` AND `errors=`."""
        text = (
            "FAIL: test_one (m.C.test_one)\n"
            "ERROR: test_two (m.C.test_two)\n"
            "Ran 4 tests in 0.010s\n\nFAILED (failures=1, errors=1)\n"
        )
        report = MC.classify_unittest(1, text, 4)
        self.assertEqual(report.outcome, MC.KILLED)
        self.assertEqual(report.deaths, ("test_one", "test_two"))

    def test_a_clean_run_survives(self) -> None:
        report = MC.classify_unittest(0, unittest_output(4, "OK"), 4)
        self.assertEqual(report.outcome, MC.SURVIVED)
        self.assertEqual(report.tests_run, 4)


# ----------------------------------------------------- classify_cargo guards


CARGO_OK = "\nrunning 2 tests\ntest a ... ok\ntest b ... ok\n\ntest result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n"


class CargoClassifierTests(unittest.TestCase):
    def test_a_lock_timeout_is_not_a_result(self) -> None:
        """Guard: 75 from cargo-serialized.sh is a missing slot, not a verdict."""
        report = MC.classify_cargo(75, CARGO_OK, 2)
        self.assertEqual(report.outcome, MC.INCONSISTENT)
        self.assertIn("slot", report.detail)

    def test_a_binary_that_started_and_never_reported_is_refused(self) -> None:
        """Guard: every `running N tests` must be matched by a `test result:`."""
        report = MC.classify_cargo(101, "\nrunning 3 tests\ntest a ... ok\n", 3)
        self.assertEqual(report.outcome, MC.INCONSISTENT)
        self.assertIn("reported a result", report.detail)

    def test_cargo_zero_tests_is_not_a_result(self) -> None:
        """Guard: `running 0 tests ... ok` exits 0 and is not a measurement."""
        text = "\nrunning 0 tests\n\ntest result: ok. 0 passed; 0 failed; 0 ignored\n"
        self.assertEqual(MC.classify_cargo(0, text, None).outcome, MC.NO_RUN)

    def test_cargo_deaths_are_counted_from_the_names_and_the_summary(self) -> None:
        """Guard: `test X ... FAILED` lines must agree with the summary's count."""
        text = (
            "\nrunning 2 tests\ntest a ... ok\ntest b ... FAILED\n\n"
            "test result: FAILED. 1 passed; 1 failed; 0 ignored\n"
        )
        report = MC.classify_cargo(101, text, 2)
        self.assertEqual(report.outcome, MC.KILLED)
        self.assertEqual(report.deaths, ("b",))

    def test_cargo_sums_across_binaries(self) -> None:
        report = MC.classify_cargo(0, CARGO_OK + CARGO_OK, 4)
        self.assertEqual(report.outcome, MC.SURVIVED)
        self.assertEqual(report.tests_run, 4)


# ------------------------------------------------------------- _apply guards


class ApplyTests(unittest.TestCase):
    def test_an_absent_anchor_is_not_a_result(self) -> None:
        """Guard: the anchor moved -- the guard was never removed."""
        _text, refusal = MC._apply("a = 1\n", MC.Mutation("l", "nowhere", "x"))
        self.assertIsNotNone(refusal)
        self.assertEqual(refusal.outcome, MC.NOT_APPLIED)
        self.assertIn("not in the subject", refusal.detail)

    def test_an_anchor_that_matches_twice_is_not_a_result(self) -> None:
        """Guard: `str.replace(..., 1)` picks the first copy and says nothing."""
        _text, refusal = MC._apply("if x:\nif x:\n", MC.Mutation("l", "if x:", "if False:"))
        self.assertIsNotNone(refusal)
        self.assertEqual(refusal.outcome, MC.AMBIGUOUS)
        self.assertIn("2 places", refusal.detail)

    def test_a_replacement_that_changes_nothing_is_not_a_result(self) -> None:
        """Guard: replace == find leaves the subject intact and looks like a run."""
        _text, refusal = MC._apply("if x:\n", MC.Mutation("l", "if x:", "if x:"))
        self.assertIsNotNone(refusal)
        self.assertEqual(refusal.outcome, MC.NOT_APPLIED)
        self.assertIn("unchanged", refusal.detail)

    def test_a_good_mutation_returns_the_mutated_text(self) -> None:
        text, refusal = MC._apply("if x:\n", MC.Mutation("l", "if x:", "if False:"))
        self.assertIsNone(refusal)
        self.assertEqual(text, "if False:\n")


# -------------------------------------------------------- build-probe guards


class BuildProbeTests(unittest.TestCase):
    """`DID NOT BUILD` has two halves and a syntax check only sees one."""

    def _tree(self, subject: str, module_body: str) -> pathlib.Path:
        tmp = tempfile.mkdtemp(prefix="mutation-build-probe-")
        work = pathlib.Path(tmp)
        (work / "subj.py").write_text(subject, encoding="utf-8")
        (work / "probe_mod.py").write_text(module_body, encoding="utf-8")
        return work

    def test_a_subject_that_does_not_parse_is_caught_without_importing_it(self) -> None:
        """Guard: py_compile. The control module never touches the subject."""
        work = self._tree("def f(\n", "VALUE = 1\n")
        built, why = MC.Unittest("probe_mod").build(work, ["subj.py"])
        self.assertFalse(built, why)
        self.assertIn("SyntaxError", why)

    def test_a_module_that_parses_but_cannot_be_imported_is_caught(self) -> None:
        """Guard: the import probe. py_compile accepts this file."""
        work = self._tree("VALUE = 1\n", "raise RuntimeError('nope')\n")
        built, why = MC.Unittest("probe_mod").build(work, ["subj.py"])
        self.assertFalse(built, why)
        self.assertIn("RuntimeError", why)

    def test_a_healthy_tree_builds(self) -> None:
        work = self._tree("VALUE = 1\n", "import subj\n")
        built, why = MC.Unittest("probe_mod").build(work, ["subj.py"])
        self.assertTrue(built, why)


class StaleBytecodeTests(unittest.TestCase):
    """Two equal-size mutants written in the same second must not share bytecode.

    Python caches compiled modules on `(source mtime in whole SECONDS, source
    size in bytes)`. Mutation testing produces equal-size mutants **by
    construction** — one fixed string replaced by another fixed string, applied
    at different sites — and a harness writes them back to back, well inside one
    second. So this is not a corner case; it is the normal case, and every
    Python mutation verdict in this repository depends on something defeating it.

    That something is the `py_compile` call in `Unittest.build`, which was
    written to catch a subject that does not parse. Its second job is invisible
    from its own code, and deleting it does not break the check it was written
    for — so this control exists to say the step is load-bearing twice.

    Measured 2026-08-20, with the recompile removed: a mutant that neuters a
    guard reports `SURVIVED`, because the run executes the **baseline's**
    bytecode. That is the harmless direction. Run the mutants in the other
    order and a mutant that changes nothing reports `KILLED`, which is the
    direction that manufactures coverage that was never measured. I hit the
    second one by hand the same day, in an ad-hoc loop with no recompile, and
    read three copies of one guard as each having its own control when two of
    the three answers were the first one's bytecode.
    """

    #: `subject.guard(-1)` must be False; the neutered mutant returns True.
    #: The comment line is padded so both mutants are byte-identical in size.
    _BASE = "# AAAA\ndef guard(x):\n    if x < 0:\n        return False\n    return True\n"
    _NEUTERED = "# AAAA\ndef guard(x):\n    if False:\n        return False\n    return True\n"
    _COMMENT_ONLY = "# BBBB\ndef guard(x):\n    if x < 0:\n        return False\n    return True\n"

    def _verdict(self, work: pathlib.Path, source: str) -> str:
        (work / "subject.py").write_text(source, encoding="utf-8")
        built, why = MC.Unittest("t_subject").build(work, ["subject.py"])
        self.assertTrue(built, why)
        return MC.Unittest("t_subject").measure(work, 1).outcome

    def test_a_neutered_guard_is_killed_even_after_a_same_size_baseline(self) -> None:
        tmp = tempfile.mkdtemp(prefix="mutation-stale-pyc-")
        work = pathlib.Path(tmp)
        (work / "t_subject.py").write_text(
            "import unittest, subject\n"
            "class T(unittest.TestCase):\n"
            "    def test_negative_is_refused(self):\n"
            "        self.assertFalse(subject.guard(-1))\n",
            encoding="utf-8",
        )
        self.assertEqual(len(self._BASE), len(self._NEUTERED))
        self.assertEqual(len(self._BASE), len(self._COMMENT_ONLY))

        self.assertEqual(self._verdict(work, self._BASE), MC.SURVIVED)
        # Same size, same second, opposite behaviour. A stale cache reports this
        # as SURVIVED — a guard the harness would report as untested.
        self.assertEqual(self._verdict(work, self._NEUTERED), MC.KILLED)
        # And back the other way: a mutant that changes nothing must not inherit
        # the KILLED verdict of the one before it. This is the dangerous
        # direction — it invents coverage.
        self.assertEqual(self._verdict(work, self._COMMENT_ONLY), MC.SURVIVED)


class AnchorFreshnessTests(unittest.TestCase):
    """`--check-anchors` must be able to FAIL, and must pass on the real tree.

    No gate runs any real mutation suite — `scripts/check.sh` and the `justfile`
    run this harness's own controls and `self-demo`. So each SUBJECT is
    mutation-checked once, by hand, at commit time, and then nothing looks
    again. When the source drifts the anchor stops matching, the mutation
    reports `NOT APPLIED`, and the suite decays to measuring nothing while its
    commit message still says "each guard killed exactly one test".

    This check builds nothing, so it is cheap enough to gate. The control below
    is a positive one: an anchor that has never been shown to fail is the
    unfalsifiable checker CLAUDE.md warns about.
    """

    def test_the_committed_anchors_are_all_fresh(self) -> None:
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            status = MC.check_anchors()
        self.assertEqual(status, 0, buf.getvalue())
        self.assertIn("|stale=0", buf.getvalue())

    def test_an_anchor_that_no_longer_matches_is_reported(self) -> None:
        drifted = MC.Mutation("drifted", "text that no subject contains", "x")
        suite = MC.SUITES["fp-width-guard"]
        MC.SUITES["drift-probe"] = (suite[0], suite[1], [("drifted", drifted.find, drifted.replace)])
        try:
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                status = MC.check_anchors()
            self.assertEqual(status, 1)
            self.assertIn("NOT APPLIED", buf.getvalue())
        finally:
            del MC.SUITES["drift-probe"]

    def test_an_anchor_matching_twice_is_reported(self) -> None:
        """`str.replace(..., 1)` would pick whichever came first and the report
        could not say which guard was deleted, so two matches is a failure."""
        suite = MC.SUITES["fp-width-guard"]
        text = (MC.ROOT / suite[0]).read_text(encoding="utf-8")
        repeated = next(line.strip() for line in text.splitlines() if text.count(line.strip()) > 1 and len(line.strip()) > 8)
        MC.SUITES["ambiguous-probe"] = (suite[0], suite[1], [("ambiguous", repeated, "x")])
        try:
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                status = MC.check_anchors()
            self.assertEqual(status, 1)
            self.assertIn("AMBIGUOUS ANCHOR", buf.getvalue())
        finally:
            del MC.SUITES["ambiguous-probe"]


# -------------------------------------------------------- end-to-end guards


class RestoreTests(unittest.TestCase):
    """The scratch tree is thrown away, but a restore that did not TAKE would let
    mutation N+1 run against mutation N's damage and report a death for it."""

    def test_a_restore_that_does_not_take_is_raised(self) -> None:
        """Guard: the restore is verified, not assumed.

        A symlink to /dev/null accepts every write and reads back empty, which
        is exactly the shape a silent restore failure has.
        """
        tmp = pathlib.Path(tempfile.mkdtemp(prefix="mutation-restore-"))
        link = tmp / "subject.py"
        link.symlink_to("/dev/null")
        with self.assertRaises(RuntimeError):
            MC._restore(link, "the original content\n")

    def test_a_restore_that_takes_is_silent(self) -> None:
        tmp = pathlib.Path(tempfile.mkdtemp(prefix="mutation-restore-"))
        path = tmp / "subject.py"
        path.write_text("mutated\n", encoding="utf-8")
        MC._restore(path, "the original content\n")
        self.assertEqual(path.read_text(encoding="utf-8"), "the original content\n")


class EndToEndTests(unittest.TestCase):
    """The slow ones: these copy the tree and run the driver for real."""

    def test_the_harness_names_all_four_outcomes(self) -> None:
        """Guard: the whole pipeline, including a mutation that targets a CONTROL."""
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            status = MC.run_demo()
        self.assertEqual(status, 0, buffer.getvalue())
        printed = buffer.getvalue()
        for expected in ("killed 1", MC.SURVIVED, MC.NO_BUILD, MC.NO_RUN):
            self.assertIn(expected, printed)

    def test_a_red_baseline_is_refused_before_any_mutation(self) -> None:
        """Guard: a suite that was already red makes every death free."""
        MC.SUITES["_control_red"] = (
            MC.DEMO_SUBJECT,
            "scripts.tests.fixtures.mutation_demo.red_tests",
            [("unreachable", "    if n < 0:", "    if False:")],
        )
        try:
            buffer = io.StringIO()
            with contextlib.redirect_stdout(buffer):
                status, reports = MC.baseline_and_mutants("_control_red")
        finally:
            del MC.SUITES["_control_red"]
        self.assertEqual(status, 1)
        self.assertEqual(reports, [])
        self.assertIn("BASELINE IS NOT GREEN", buffer.getvalue())

    def test_a_baseline_that_does_not_build_is_refused(self) -> None:
        """Guard: the build probe runs on the baseline, before any mutation."""
        MC.SUITES["_control_unbuildable"] = (
            MC.DEMO_SUBJECT,
            "scripts.tests.fixtures.mutation_demo.import_error_tests",
            [("unreachable", "    if n < 0:", "    if False:")],
        )
        try:
            buffer = io.StringIO()
            with contextlib.redirect_stdout(buffer):
                status, reports = MC.baseline_and_mutants("_control_unbuildable")
        finally:
            del MC.SUITES["_control_unbuildable"]
        self.assertEqual(status, 1)
        self.assertEqual(reports, [])
        self.assertIn("BASELINE DID NOT BUILD", buffer.getvalue())



class ExitStatusTests(unittest.TestCase):
    """"the guard is not tested" and "the harness could not tell" are different
    failures, and neither may be swallowed by the other's absence."""

    def _run(self, name: str, mutations: list[tuple[str, ...]]) -> tuple[int, str]:
        MC.SUITES[name] = (
            MC.DEMO_SUBJECT,
            "scripts.tests.fixtures.mutation_demo.suite_tests",
            mutations,
        )
        try:
            buffer = io.StringIO()
            with contextlib.redirect_stdout(buffer):
                status, reports = MC.baseline_and_mutants(name)
        finally:
            del MC.SUITES[name]
        self.assertEqual(len(reports), len(mutations), buffer.getvalue())
        return status, buffer.getvalue()

    def test_an_unmeasured_mutation_alone_fails_the_run(self) -> None:
        """Guard: a DID NOT BUILD with no survivor anywhere still exits nonzero."""
        status, printed = self._run(
            "_control_unmeasured_only",
            [("breaks the parse", "def classify(n: int) -> str:", "def classify(n: int) -> str")],
        )
        self.assertIn(MC.NO_BUILD, printed)
        self.assertNotIn("not covered by any test", printed)
        self.assertEqual(status, 1, printed)

    def test_a_survivor_alone_fails_the_run(self) -> None:
        """Guard: a SURVIVED with nothing unmeasured anywhere still exits nonzero."""
        status, printed = self._run(
            "_control_survivor_only",
            [("a guard NO control drives", "    if n > 100:", "    if False:")],
        )
        self.assertIn("not covered by any test", printed)
        self.assertNotIn("NOT MEASURED", printed)
        self.assertEqual(status, 1, printed)

    def test_a_clean_suite_exits_zero(self) -> None:
        status, printed = self._run(
            "_control_all_killed",
            [("a guard a control drives", "    if n < 0:", "    if False:")],
        )
        self.assertEqual(status, 0, printed)


if __name__ == "__main__":
    unittest.main()
