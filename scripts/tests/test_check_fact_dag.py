"""Controls for `check-fact-dag.py`.

It passes on the committed ledger, so on its own that proves nothing. Each
guard is driven to fail here, including the two that exist because a *measuring*
tool can mislead: a dangling `depends_on` must not be counted as connectivity,
and a loader that stops finding facts must not report a healthy zero.
"""

from __future__ import annotations

import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_fact_dag", ROOT / "scripts" / "check-fact-dag.py"
)
assert SPEC and SPEC.loader
FD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FD)


def ledger(pairs: dict[str, list[str]]) -> dict[str, dict]:
    return {i: {"id": i, "depends_on": d} for i, d in pairs.items()}


def padded(pairs: dict[str, list[str]], total: int) -> dict[str, dict]:
    """`pairs` plus enough linked filler to clear the MIN_FACTS floor."""
    out = dict(pairs)
    for i in range(total - len(pairs)):
        out[f"F:filler-root-{i}"] = []
        out[f"F:filler-leaf-{i}"] = [f"F:filler-root-{i}"]
    return ledger(out)


class TheShapeIsMeasuredNotAssumed(unittest.TestCase):
    def test_a_chain_is_counted_at_its_real_depth(self) -> None:
        stats = FD.shape(ledger({"a": [], "b": ["a"], "c": ["b"], "d": ["c"]}))
        self.assertEqual(stats["max_depth"], 4)
        self.assertEqual(stats["isolated"], 0)

    def test_isolated_facts_are_those_with_neither_direction(self) -> None:
        stats = FD.shape(ledger({"a": [], "b": ["a"], "lonely": []}))
        self.assertEqual(stats["isolated"], 1)

    def test_a_dangling_reference_is_not_connectivity(self) -> None:
        """The measurement trap: `b` names a fact that does not exist. If that
        counted as a dependency, `b` would look connected and the isolated
        fraction would be understated — the tool flattering itself."""
        stats = FD.shape(ledger({"a": [], "b": ["F:does-not-exist"]}))
        self.assertEqual(stats["dangling"], ["b -> F:does-not-exist"])
        self.assertEqual(stats["isolated"], 2)

    def test_a_cycle_does_not_hang_or_report_infinite_depth(self) -> None:
        stats = FD.shape(ledger({"a": ["b"], "b": ["a"]}))
        self.assertGreaterEqual(stats["max_depth"], 1)


class EachGuardCanFail(unittest.TestCase):
    def test_too_many_isolated_facts_trips_the_ratchet(self) -> None:
        facts = padded({f"F:lonely-{i}": [] for i in range(200)}, 200)
        failures = FD.evaluate(FD.shape(facts))
        self.assertTrue(any("isolated" in f for f in failures), failures)

    def test_a_well_connected_ledger_passes(self) -> None:
        failures = FD.evaluate(FD.shape(padded({}, 120)))
        self.assertEqual(failures, [])

    def test_a_dangling_edge_fails(self) -> None:
        facts = padded({"F:broken": ["F:missing"]}, 120)
        failures = FD.evaluate(FD.shape(facts))
        self.assertTrue(any("does not exist" in f for f in failures), failures)

    def test_an_empty_ledger_fails_instead_of_reporting_health(self) -> None:
        """A loader pointed at the wrong tree finds nothing, and 0 isolated of 0
        is a perfect score. The floor is what makes that a failure."""
        failures = FD.evaluate(FD.shape(ledger({"a": []})))
        self.assertTrue(any("stopped parsing" in f for f in failures), failures)

    def test_the_committed_ledger_passes(self) -> None:
        self.assertEqual(FD.main(["--quiet"]), 0)


if __name__ == "__main__":
    unittest.main()
