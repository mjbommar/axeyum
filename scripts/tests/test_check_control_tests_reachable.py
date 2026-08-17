"""Controls for `check-control-tests-reachable.py`.

The gate passes on the committed tree, which proves nothing on its own — it is a
ratchet sitting exactly at its baseline, the state where an off-by-one in either
direction is invisible. So every guard is driven to failure here, and the
distinction the gate rests on — *running* a module versus *mentioning* it — is
pinned in both directions.
"""

from __future__ import annotations

import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_control_tests_reachable",
    ROOT / "scripts" / "check-control-tests-reachable.py",
)
assert SPEC and SPEC.loader
CT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CT)


class RunningAModuleIsNotTheSameAsMentioningIt(unittest.TestCase):
    """The whole gate rests on this distinction. If it blurs, a control that is
    only cited in a status table counts as covered."""

    MODS = {"test_check_fact_dag", "test_parity_evidence"}

    def test_a_module_on_a_unittest_line_is_run(self) -> None:
        line = "    python3 -m unittest scripts.tests.test_check_fact_dag"
        self.assertEqual(CT.modules_run_by(self.MODS, line), {"test_check_fact_dag"})

    def test_a_module_on_a_pytest_line_is_run(self) -> None:
        line = "  pytest scripts/tests/test_parity_evidence.py -q"
        self.assertEqual(CT.modules_run_by(self.MODS, line), {"test_parity_evidence"})

    def test_a_module_merely_mentioned_in_prose_is_not_run(self) -> None:
        """The control. A doc sentence naming a test is not coverage."""
        prose = "See `scripts/tests/test_check_fact_dag` for the DAG controls."
        self.assertEqual(CT.modules_run_by(self.MODS, prose), set())

    def test_a_mention_and_a_run_in_one_file_still_counts_as_run(self) -> None:
        text = (
            "# test_parity_evidence explains the parity rows\n"
            "python3 -m unittest scripts.tests.test_parity_evidence\n"
        )
        self.assertEqual(CT.modules_run_by(self.MODS, text), {"test_parity_evidence"})


class TheRatchetFires(unittest.TestCase):
    @staticmethod
    def _mods(n: int) -> set[str]:
        return {f"test_m{i}" for i in range(n)}

    def test_one_new_orphan_above_the_baseline_fails(self) -> None:
        mods = self._mods(CT.MIN_MODULES + CT.ORPHAN_BASELINE + 1)
        runs = {m: {"justfile"} for m in sorted(mods)[: CT.MIN_MODULES]}
        failures = CT.evaluate(mods, runs)
        self.assertTrue(failures)
        self.assertIn("executed by nothing", failures[0])

    def test_sitting_exactly_at_the_baseline_passes(self) -> None:
        mods = self._mods(CT.MIN_MODULES + CT.ORPHAN_BASELINE)
        runs = {m: {"justfile"} for m in sorted(mods)[: CT.MIN_MODULES]}
        self.assertEqual(CT.evaluate(mods, runs), [])

    def test_wiring_an_orphan_up_is_never_a_failure(self) -> None:
        mods = self._mods(CT.MIN_MODULES + CT.ORPHAN_BASELINE)
        runs = {m: {"justfile"} for m in mods}
        self.assertEqual(CT.evaluate(mods, runs), [])

    def test_a_collapsed_glob_fails_instead_of_reporting_zero_orphans(self) -> None:
        """Vacuity guard. With no modules found, every module is trivially
        'executed' and the gate would report a perfect score."""
        failures = CT.evaluate(set(), {})
        self.assertTrue(failures)
        self.assertIn("stopped matching", failures[0])

    def test_the_vacuity_guard_outranks_the_ratchet(self) -> None:
        """A broken glob must not be reported as an orphan regression; the
        message a maintainer sees decides whether they go looking for the right
        thing."""
        failures = CT.evaluate(self._mods(3), {})
        self.assertEqual(len(failures), 1)
        self.assertIn("stopped matching", failures[0])


class TheCommittedTreeIsMeasuredNotAssumed(unittest.TestCase):
    def test_the_baseline_matches_what_is_actually_there(self) -> None:
        """A baseline above the real count would silently allow new orphans."""
        mods = CT.modules()
        runs = CT.executed(mods, CT.tracked())
        self.assertEqual(
            len(mods - set(runs)),
            CT.ORPHAN_BASELINE,
            "the orphan count moved; if it FELL, lower ORPHAN_BASELINE in the same "
            "commit so the gain is locked in",
        )

    def test_this_very_control_file_is_not_itself_an_orphan(self) -> None:
        """The gate would be absurd if its own controls were unrun."""
        mods = CT.modules()
        runs = CT.executed(mods, CT.tracked())
        self.assertTrue(
            "test_check_control_tests_reachable" in runs,
            "this gate's own controls are executed by nothing; wire them into "
            "`justfile` and `scripts/check.sh`",
        )


if __name__ == "__main__":
    unittest.main()
