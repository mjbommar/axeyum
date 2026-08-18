"""Controls for `check-smt-evidence-certified.py`.

The check passes on the committed ledger, which on its own proves nothing --
that is exactly the failure mode it exists to catch. So every guard is driven to
fail here, and each test trips **one** guard: delete any single guard from
`evaluate` / `probe_failures` and exactly one test below dies.

The two tests that matter most are the ones about not-knowing. A missing
`; evidence` line and a missing negative control both leave the checker unable
to tell certified from uncertified, and both must fail rather than pass.
"""

from __future__ import annotations

import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_smt_evidence_certified", ROOT / "scripts" / "check-smt-evidence-certified.py"
)
assert SPEC and SPEC.loader
CE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CE)


def good(path: str = "x.smt2") -> dict:
    return {
        "path": path,
        "verdict": "unsat",
        "kind": "unsat-term-level",
        "certified": "1",
    }


def rows(n: int | None = None) -> list[dict]:
    """A healthy row set that clears the floor."""
    count = CE.MIN_INSTANCES + 2 if n is None else n
    return [good(f"i{i}.smt2") for i in range(count)]


CONTROL = {
    "path": CE.PROBE,
    "verdict": "unsat",
    "kind": "unsat-uncertified",
    "certified": "0",
}


class AHealthyLedgerPasses(unittest.TestCase):
    def test_certified_rows_with_a_discriminating_control_pass(self) -> None:
        self.assertEqual(CE.evaluate(rows(), CONTROL), [])


class EachGuardCanFail(unittest.TestCase):
    def test_too_few_instances_fails_instead_of_reporting_health(self) -> None:
        failures = CE.evaluate(rows(3), CONTROL)
        self.assertTrue(any("floor" in f for f in failures), failures)

    def test_a_non_unsat_verdict_fails(self) -> None:
        bad = rows()
        bad[0] = good() | {"verdict": "sat"}
        failures = CE.evaluate(bad, CONTROL)
        self.assertTrue(any("expected unsat" in f for f in failures), failures)

    def test_a_missing_evidence_line_fails_rather_than_passing(self) -> None:
        """'Could not tell' must not read as 'certified'."""
        bad = rows()
        bad[0] = good() | {"kind": None, "certified": None}
        failures = CE.evaluate(bad, CONTROL)
        self.assertTrue(any("could not be read" in f for f in failures), failures)

    def test_an_uncertified_settled_fact_fails(self) -> None:
        """The defect this whole check exists for: right verdict, no object."""
        bad = rows()
        bad[0] = good() | {"kind": "unsat-uncertified", "certified": "0"}
        failures = CE.evaluate(bad, CONTROL)
        self.assertTrue(any("UNCERTIFIED" in f for f in failures), failures)

    def test_a_missing_negative_control_fails(self) -> None:
        failures = CE.evaluate(rows(), None)
        self.assertTrue(any("has no" in f and "distinguish" in f for f in failures), failures)

    def test_a_control_that_stopped_being_refuted_fails(self) -> None:
        """It only discriminates while it is genuinely unsat."""
        failures = CE.evaluate(rows(), CONTROL | {"verdict": "unknown"})
        self.assertTrue(any("no longer calibrated" in f for f in failures), failures)

    def test_a_control_that_became_certified_fails_as_an_action(self) -> None:
        """The one failure that is good news: the gap closed, so close the fact
        and repoint the control. Left alone it would silently stop
        discriminating, and the check would be self-confirming again."""
        certified_now = CONTROL | {"kind": "unsat-term-level", "certified": "1"}
        failures = CE.evaluate(rows(), certified_now)
        self.assertTrue(any("GOOD NEWS" in f for f in failures), failures)


class TheExtractorSelectsTheRightFacts(unittest.TestCase):
    def test_the_committed_ledger_yields_the_measured_instance_count(self) -> None:
        found = CE.instances()
        self.assertGreaterEqual(len(found), CE.MIN_INSTANCES, found)
        self.assertTrue(all(p.endswith(".smt2") for _, p in found))

    def test_the_negative_control_is_not_a_ledger_evidence_instance(self) -> None:
        """A mutation control must not force a mathematical fact to stay open."""
        self.assertNotIn(CE.PROBE, [p for _, p in CE.instances()])


if __name__ == "__main__":
    unittest.main()
