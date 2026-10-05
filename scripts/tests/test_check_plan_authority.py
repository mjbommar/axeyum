"""Controls for the PLAN.md budget in ``scripts/check-plan-authority.py``.

Each test builds a minimal tree that is within budget except for exactly one
violation, and asserts that exactly one error naming that violation comes back.
Deleting any one guard in ``budget_errors`` makes exactly one test fail.
"""

from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_plan_authority", ROOT / "scripts" / "check-plan-authority.py"
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def lane(status: str = "WIP", padding: int = 0) -> str:
    return (
        "# Lane: x\n\n<!-- plan-section: lane-status -->\n\n"
        f"**Lane block (`{status}`, x, 2026-10-05).** Next: something.\n"
        + ("y" * padding)
    )


class BudgetTests(unittest.TestCase):
    def tree(self, lanes: dict[str, str], global_bytes: int = 100, plan_bytes: int = 100) -> Path:
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        root = Path(scratch.name)
        (root / "docs/plan/status").mkdir(parents=True)
        (root / "docs/plan/global").mkdir(parents=True)
        (root / "docs/plan/status/README.md").write_text("x" * 10_000)  # never counted
        (root / "docs/plan/global/README.md").write_text("x" * 50_000)  # never counted
        (root / "docs/plan/global/00-header.md").write_text("g" * global_bytes)
        for name, body in lanes.items():
            (root / f"docs/plan/status/{name}.md").write_text(body)
        (root / "PLAN.md").write_text("p" * plan_bytes)
        return root

    def test_within_budget_is_clean(self) -> None:
        self.assertEqual(MODULE.budget_errors(self.tree({"a": lane(), "b": lane("PAUSED")})), [])

    def test_lane_over_its_cap(self) -> None:
        errors = MODULE.budget_errors(self.tree({"a": lane(padding=MODULE.LANE_CAP)}))
        self.assertEqual(len(errors), 1)
        self.assertIn("status/a.md is", errors[0])

    def test_done_lane_must_be_archived(self) -> None:
        errors = MODULE.budget_errors(self.tree({"a": lane("DONE"), "b": lane()}))
        self.assertEqual(len(errors), 1)
        self.assertIn("archive-plan-lane.py a", errors[0])

    def test_too_many_active_lanes(self) -> None:
        lanes = {f"l{i:02d}": lane() for i in range(MODULE.MAX_ACTIVE_LANES + 1)}
        errors = MODULE.budget_errors(self.tree(lanes))
        self.assertEqual(len(errors), 1)
        self.assertIn("lane files in docs/plan/status/", errors[0])

    def test_global_over_its_cap(self) -> None:
        errors = MODULE.budget_errors(self.tree({}, global_bytes=MODULE.GLOBAL_CAP + 1))
        self.assertEqual(len(errors), 1)
        self.assertIn("docs/plan/global/ totals", errors[0])

    def test_rendered_plan_over_fixed_ceiling(self) -> None:
        ceiling = MODULE.GLOBAL_CAP + MODULE.LANE_CAP * MODULE.MAX_ACTIVE_LANES
        errors = MODULE.budget_errors(self.tree({}, plan_bytes=ceiling + 1))
        self.assertEqual(len(errors), 1)
        self.assertIn("PLAN.md is", errors[0])


class InstructionSyncTests(unittest.TestCase):
    def pair(self, claude_body: str, agents_body: str) -> Path:
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        root = Path(scratch.name)
        (root / "CLAUDE.md").write_text("# CLAUDE.md\n\nGuidance for Claude.\n" + claude_body)
        (root / "AGENTS.md").write_text("# AGENTS.md\n\nGuidance for Codex.\n" + agents_body)
        return root

    def test_same_body_passes(self) -> None:
        self.assertEqual(MODULE.instruction_sync_errors(self.pair("rule\n", "rule\n")), [])

    def test_drifted_body_fails(self) -> None:
        errors = MODULE.instruction_sync_errors(self.pair("rule\n", "old rule\n"))
        self.assertEqual(len(errors), 1)


if __name__ == "__main__":
    unittest.main()
