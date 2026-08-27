#!/usr/bin/env python3
"""Controls for `scripts/run-python-controls.py`, the catch-all control runner.

This suite is itself run by nothing that names it -- which is the point. It is
discovered and executed by the very script it tests, so the demonstration and
the subject are the same object: if the discovery breaks, this suite stops
running, and `scripts/check-control-registration.sh`'s G7 cross-check notices
that the two partitions disagree.

The subject is loaded BY PATH, not imported. `run-python-controls.py` has
hyphens in its name so `import` cannot reach it -- the same reason
`scripts/tests/test_validate_facts_allowlist.py` loads its subject by path.
Loading the real module matters here: two test files on 2026-08-27 defined
their own copies of a regex and asserted against those, importing nothing, so
deleting a namespace from the real validator left them exiting 0 while
reporting "15/15 guards verified". A test that restates its subject is testing
the restatement.

Every case below is one the runner must REJECT, plus a healthy corpus it must
ACCEPT -- a case that passes in both worlds is not a control.
"""

from __future__ import annotations

import importlib.util
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

REPO = pathlib.Path(__file__).resolve().parents[2]
SUBJECT = REPO / "scripts" / "run-python-controls.py"

_spec = importlib.util.spec_from_file_location("run_python_controls", SUBJECT)
assert _spec is not None and _spec.loader is not None
RPC = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(RPC)


SUITE_BODY = """import unittest


class T(unittest.TestCase):
    def test_a(self) -> None:
        self.assertTrue(True)

    def test_b(self) -> None:
        self.assertTrue(True)
"""

FAILING_BODY = """import unittest


class T(unittest.TestCase):
    def test_a(self) -> None:
        self.assertTrue(False, "this control is supposed to fail")
"""

# Bare module-level functions with no `TestCase`: the pytest dialect. `python3
# -m unittest` collects NOTHING from this and exits 5. Ten of the 188 orphan
# suites measured on 2026-08-27 had exactly this shape.
VACUOUS_BODY = """def test_a() -> None:
    assert True
"""


def build_corpus(root: pathlib.Path, n: int = 205) -> None:
    """A skeleton repo big enough to clear the runner's own corpus floors."""
    (root / "scripts" / "tests").mkdir(parents=True, exist_ok=True)
    (root / "hooks").mkdir(exist_ok=True)
    for i in range(n):
        (root / "scripts" / "tests" / f"test_gen_{i}.py").write_text(SUITE_BODY)
    (root / "scripts" / "check.sh").write_text("#!/usr/bin/env bash\nexit 0\n")
    (root / "justfile").write_text("check:\n\techo hi\n")
    (root / "hooks" / "pre-push").write_text("#!/usr/bin/env bash\nexit 0\n")
    (root / "scripts" / "control-optout.tsv").write_text("# none\n")


class Sandbox:
    """Point the real module's module-level paths at a scratch tree."""

    def __init__(self, root: pathlib.Path) -> None:
        self.root = root

    def __enter__(self):
        self.saved = (RPC.ROOT, RPC.TESTS, RPC.OPTOUT)
        RPC.ROOT = self.root
        RPC.TESTS = self.root / "scripts" / "tests"
        RPC.OPTOUT = self.root / "scripts" / "control-optout.tsv"
        return self

    def __exit__(self, *exc):
        RPC.ROOT, RPC.TESTS, RPC.OPTOUT = self.saved
        return False


class OptoutParsingTests(unittest.TestCase):
    """`scripts/control-optout.tsv` is the authority that replaced an
    unexplained numeric floor of 188. Every way it can be malformed is a way
    that floor comes back."""

    def setUp(self) -> None:
        self.tmp = pathlib.Path(tempfile.mkdtemp(prefix="rpc-optout-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)
        build_corpus(self.tmp, n=205)

    def write_optout(self, text: str) -> None:
        (self.tmp / "scripts" / "control-optout.tsv").write_text(text)

    def test_positive_control_a_well_formed_list_parses(self) -> None:
        self.write_optout("# comment\n\ntest_gen_1\tbecause reasons\n")
        with Sandbox(self.tmp):
            self.assertEqual(RPC.read_optout(), {"test_gen_1": "because reasons"})

    def test_entry_without_a_tab_is_rejected(self) -> None:
        self.write_optout("test_gen_1 because reasons\n")
        with Sandbox(self.tmp), self.assertRaisesRegex(RPC.ControlError, "no TAB"):
            RPC.read_optout()

    def test_entry_without_a_reason_is_rejected(self) -> None:
        self.write_optout("test_gen_1\t\n")
        with Sandbox(self.tmp), self.assertRaisesRegex(RPC.ControlError, "has no reason"):
            RPC.read_optout()

    def test_duplicate_entry_is_rejected(self) -> None:
        self.write_optout("test_gen_1\ta\ntest_gen_1\tb\n")
        with Sandbox(self.tmp), self.assertRaisesRegex(RPC.ControlError, "listed twice"):
            RPC.read_optout()

    def test_missing_optout_file_is_an_error_not_an_empty_list(self) -> None:
        (self.tmp / "scripts" / "control-optout.tsv").unlink()
        with Sandbox(self.tmp), self.assertRaisesRegex(RPC.ControlError, "missing"):
            RPC.read_optout()

    def test_stale_entry_naming_a_deleted_suite_fails_the_run(self) -> None:
        """Fails in the OTHER direction: an allowlist that only ever grows is
        where dead entries hide."""
        self.write_optout("test_gen_does_not_exist\tstale\n")
        with Sandbox(self.tmp):
            _, _, _, stale = RPC.partition()
            self.assertEqual(stale, ["test_gen_does_not_exist"])
            rc = self.run_main([])
            self.assertEqual(rc, 2)

    def run_main(self, argv: list[str]) -> int:
        saved = sys.argv
        sys.argv = ["run-python-controls.py", *argv]
        try:
            with Sandbox(self.tmp):
                return RPC.main()
        finally:
            sys.argv = saved


class PartitionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = pathlib.Path(tempfile.mkdtemp(prefix="rpc-part-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)
        build_corpus(self.tmp, n=205)

    def test_both_invocation_forms_count_as_named(self) -> None:
        """A suite run as `python3 scripts/tests/x.py` is as run as one named
        `python3 -m unittest scripts.tests.x`. Counting only the module form
        overcounted orphans by 18 when this logic first landed."""
        (self.tmp / "scripts" / "check.sh").write_text(
            "python3 -m unittest scripts.tests.test_gen_1\n"
            "python3 scripts/tests/test_gen_2.py\n"
        )
        with Sandbox(self.tmp):
            mine, named, _, _ = RPC.partition()
        self.assertEqual(named, {"test_gen_1", "test_gen_2"})
        self.assertNotIn("test_gen_1", mine)
        self.assertNotIn("test_gen_2", mine)
        self.assertIn("test_gen_3", mine)

    def test_a_comment_is_not_a_caller(self) -> None:
        """The registration gate shipped with exactly this hole: a
        `# Control: scripts/tests/...` line satisfied a plain `grep -F`, so a
        control that nothing ran reported as registered."""
        (self.tmp / "scripts" / "check.sh").write_text(
            "  # python3 -m unittest scripts.tests.test_gen_1\n"
        )
        with Sandbox(self.tmp):
            _, named, _, _ = RPC.partition()
        self.assertEqual(named, set())

    def test_opted_out_suites_are_not_run(self) -> None:
        (self.tmp / "scripts" / "control-optout.tsv").write_text("test_gen_7\tnope\n")
        with Sandbox(self.tmp):
            mine, _, optout, _ = RPC.partition()
        self.assertIn("test_gen_7", optout)
        self.assertNotIn("test_gen_7", mine)

    def test_an_implausibly_small_corpus_is_loud_not_green(self) -> None:
        """A glob that stops matching exits 0 in every naive implementation of
        this script. That is the failure it exists to prevent."""
        for f in (self.tmp / "scripts" / "tests").glob("test_gen_*.py"):
            f.unlink()
        (self.tmp / "scripts" / "tests" / "test_gen_0.py").write_text(SUITE_BODY)
        with Sandbox(self.tmp), self.assertRaisesRegex(RPC.ControlError, "found only 1 suite"):
            RPC.partition()

    def test_hyphenated_py_controls_are_reported(self) -> None:
        """Unreachable twice over: invisible to the `test_*.py` glob AND not an
        importable module name."""
        (self.tmp / "scripts" / "tests" / "test-hyphen-probe.py").write_text(SUITE_BODY)
        with Sandbox(self.tmp):
            self.assertEqual(RPC.hyphenated_py(), ["test-hyphen-probe.py"])


class EndToEndTests(unittest.TestCase):
    """The runner's teeth: it must go red on a failing suite AND on a suite
    that collects nothing. The second is the repository's oldest trap."""

    def setUp(self) -> None:
        self.tmp = pathlib.Path(tempfile.mkdtemp(prefix="rpc-e2e-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)
        build_corpus(self.tmp, n=205)

    def run_it(self) -> subprocess.CompletedProcess:
        shutil.copy(SUBJECT, self.tmp / "scripts" / "run-python-controls.py")
        return subprocess.run(
            [sys.executable, "-B", str(self.tmp / "scripts" / "run-python-controls.py")],
            cwd=self.tmp,
            capture_output=True,
            text=True,
            timeout=600,
        )

    def test_positive_control_a_healthy_corpus_passes(self) -> None:
        p = self.run_it()
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("suites=205", p.stdout)
        self.assertIn("tests=410", p.stdout)

    def test_a_failing_suite_turns_the_run_red(self) -> None:
        (self.tmp / "scripts" / "tests" / "test_gen_3.py").write_text(FAILING_BODY)
        p = self.run_it()
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("test_gen_3 FAILED", p.stderr)

    def test_a_suite_that_collects_zero_tests_turns_the_run_red(self) -> None:
        (self.tmp / "scripts" / "tests" / "test_gen_4.py").write_text(VACUOUS_BODY)
        p = self.run_it()
        self.assertNotEqual(p.returncode, 0, p.stdout + p.stderr)
        # The specific message, not merely a nonzero exit: a vacuous suite exits
        # 5 on Python >= 3.12 and would land in the generic `failed` bucket
        # otherwise, so asserting only "red" leaves the zero-tests guard
        # unverified. Mutation-checked: dropping the `vacuous` partition makes
        # this case die and the generic one stay green.
        self.assertIn("ran ZERO tests", p.stderr)
        self.assertIn("test_gen_4", p.stderr)
        self.assertIn("vacuous=1", p.stdout)

    def test_a_corpus_that_collects_almost_nothing_hits_the_test_floor(self) -> None:
        """The suite COUNT can hold while every suite silently collects nothing,
        so the two floors are independent and this one needs its own case. It
        survived the first mutation round -- a guard nothing kills is
        decoration, and this is what stopped it being one. Exit 2 (structural),
        deliberately distinct from exit 1 (a control found something)."""
        for f in (self.tmp / "scripts" / "tests").glob("test_gen_*.py"):
            f.write_text(VACUOUS_BODY)
        p = self.run_it()
        self.assertEqual(p.returncode, 2, p.stdout[-2000:])
        self.assertIn("below the floor", p.stderr)


if __name__ == "__main__":
    unittest.main()
