"""Guards on the action `gen-dominance-scoreboard.py` prints for an audited row.

The action string is the only place the scoreboard tells a reader that a row's
audit went wrong. It read `summary.timeouts`, which counts ONLY the audited
population -- so a directory-backed row that timed out on every instance it
excluded published `timeouts: 0` and an action of "dominant on audited row".
Each guard below was deleted in turn; the mutation results are in the commit
that added this file.
"""

import importlib.util
import sys
import unittest
from pathlib import Path

SCRIPT = Path(__file__).parents[1] / "gen-dominance-scoreboard.py"
SPEC = importlib.util.spec_from_file_location("gen_dominance_scoreboard", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
# Registered BEFORE exec: the module defines a frozen `@dataclass`, and
# `dataclasses` resolves field types through `sys.modules[cls.__module__]`.
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)

ROW = {"file": "bench-results/baselines/row.json", "decided": 4}


def route() -> object:
    return MODULE.ProofRoute(
        lane="test", status="strong", next_action="", lean_candidate=True
    )


def audit(**summary) -> dict:
    base = {
        "audit_errors": 0,
        "timeouts": 0,
        "audited_unsat": 2,
        "lean_checked_unsat": 2,
        "dominant_candidates": 4,
        "audited_decided": 4,
    }
    excluded = summary.pop("excluded", None)
    base.update(summary)
    if excluded is not None:
        base["excluded_from_audited"] = excluded
    return {"complete_audit": True, "summary": base}


class ExactDominanceAction(unittest.TestCase):
    def action(self, **kwargs) -> str:
        return MODULE.exact_dominance_action(ROW, audit(**kwargs), route())

    def test_a_clean_row_is_dominant(self):
        # POSITIVE CONTROL. Without it, a guard that returns a complaint
        # unconditionally would pass every test below.
        self.assertEqual(self.action(), "dominant on audited row")

    def test_a_clean_row_with_an_empty_excluded_block_is_still_dominant(self):
        # Schema v4 emits the block on every row, zeroed. Presence must not be
        # read as a finding.
        self.assertEqual(
            self.action(
                excluded={
                    "total": 0,
                    "audit_undecided": 0,
                    "audit_undecided_timeouts": 0,
                    "audit_undecided_errors": 0,
                }
            ),
            "dominant on audited row",
        )

    def test_an_audited_error_is_reported(self):
        # This guard predates the excluded-instance work and NOTHING covered
        # it: deleting `summary.get("audit_errors", 0)` killed zero tests.
        self.assertEqual(self.action(audit_errors=1), "fix audit errors")

    def test_an_audited_timeout_is_reported(self):
        self.assertEqual(self.action(timeouts=1), "fix audit timeouts")

    def test_a_timeout_among_the_EXCLUDED_instances_is_reported(self):
        # The defect: `timeouts` is 0 and the row is not clean.
        self.assertEqual(
            self.action(
                excluded={"audit_undecided": 1, "audit_undecided_timeouts": 1}
            ),
            "fix audit timeouts",
        )

    def test_an_error_among_the_EXCLUDED_instances_is_reported(self):
        self.assertEqual(
            self.action(
                excluded={"audit_undecided": 1, "audit_undecided_errors": 1}
            ),
            "fix audit errors",
        )

    def test_an_excluded_undecided_instance_is_reported_even_without_a_timeout(self):
        # An instance the audit declined -- neither a timeout nor an error --
        # still shrank the row's population and must not read as dominant.
        self.assertEqual(
            self.action(excluded={"audit_undecided": 1}),
            "audit undecided instances excluded from the row",
        )


if __name__ == "__main__":
    unittest.main()
