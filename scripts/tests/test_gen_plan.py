"""Focused tests for the generated PLAN.md.

Each test is a control for exactly one guard in ``scripts/gen-plan.py``;
``scripts/tests/mutation_controls.py plan`` deletes the guards one at a time and
requires each deletion to kill a test.
"""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "gen-plan.py"
SPEC = importlib.util.spec_from_file_location("gen_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def lane(sections: dict[str, str], name: str = "10-a") -> dict[str, object]:
    return {"path": f"{name}.md", "lane": name, "sections": dict(sections)}


MINIMAL_GLOBAL = [
    (
        "00-header.md",
        "# Axeyum plan, status, and next actions\n\n**Canonical project tracker.**\n",
    ),
    ("10-status.md", "## Status\n\n<!-- plan-generated: landed-changes -->\n"),
    (
        "20-rest.md",
        "## Next Actions\n\n<!-- plan-generated: lane-status -->\n\n"
        "## Workstream state\n\n## Resume protocol\n\n## Planning rules\n",
    ),
]


class LaneFileTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = TemporaryDirectory()
        self.dir = Path(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)

    def write(self, text: str) -> Path:
        path = self.dir / "10-lane.md"
        path.write_text(text, encoding="utf-8")
        return path

    def test_lane_file_must_name_itself_with_a_heading(self) -> None:
        with self.assertRaises(MODULE.PlanError) as caught:
            MODULE.read_lane(self.write("<!-- plan-section: lane-status -->\n\nbody\n"))
        self.assertIn("heading naming the lane", str(caught.exception))

    def test_unknown_section_name_is_rejected(self) -> None:
        with self.assertRaises(MODULE.PlanError) as caught:
            MODULE.read_lane(self.write("# Lane: a\n\n<!-- plan-section: next-steps -->\n\nx\n"))
        self.assertIn("unknown section", str(caught.exception))

    def test_repeated_section_is_rejected(self) -> None:
        with self.assertRaises(MODULE.PlanError) as caught:
            MODULE.read_lane(
                self.write(
                    "# Lane: a\n\n<!-- plan-section: lane-status -->\n\nfirst\n\n"
                    "<!-- plan-section: lane-status -->\n\nsecond\n"
                )
            )
        self.assertIn("appears twice", str(caught.exception))

    def test_text_before_the_first_marker_is_rejected(self) -> None:
        # It would be silently dropped, which is the failure mode this whole
        # change exists to remove.
        with self.assertRaises(MODULE.PlanError) as caught:
            MODULE.read_lane(
                self.write("# Lane: a\n\nan orphaned note\n\n<!-- plan-section: lane-status -->\n\nx\n")
            )
        self.assertIn("would never be emitted", str(caught.exception))

    def test_sections_are_split_and_stripped(self) -> None:
        parsed = MODULE.read_lane(
            self.write(
                "# Lane: a\n\n<!-- plan-section: lane-status -->\n\n**block**\n\n"
                "<!-- plan-section: landed-changes -->\n\n| 2026-08-14 | `a` | b |\n"
            )
        )
        self.assertEqual(parsed["sections"]["lane-status"], "**block**")
        self.assertEqual(parsed["sections"]["landed-changes"], "| 2026-08-14 | `a` | b |")


class LandedRowTests(unittest.TestCase):
    def test_malformed_row_is_rejected(self) -> None:
        with self.assertRaises(MODULE.PlanError) as caught:
            MODULE.collect_landed([lane({"landed-changes": "landed something last week"})])
        self.assertIn("YYYY-MM-DD", str(caught.exception))

    def test_rows_merge_newest_first_across_lanes(self) -> None:
        rows = MODULE.collect_landed(
            [
                lane({"landed-changes": "| 2026-08-07 | `old` | x |"}, "20-b"),
                lane({"landed-changes": "| 2026-08-14 | `new` | y |"}, "10-a"),
            ]
        )
        self.assertEqual([row["date"] for row in rows], ["2026-08-14", "2026-08-07"])

    def test_same_day_rows_from_two_lanes_have_a_total_order(self) -> None:
        # Without the lane/ordinal tiebreak this is whatever order the lanes
        # arrived in, so the merge would not be reproducible.
        rows = [
            {"date": "2026-08-14", "lane": "20-b", "ordinal": 0, "text": "b"},
            {"date": "2026-08-14", "lane": "10-a", "ordinal": 1, "text": "a1"},
            {"date": "2026-08-14", "lane": "10-a", "ordinal": 0, "text": "a0"},
        ]
        self.assertEqual(
            [row["text"] for row in sorted(rows, key=MODULE.landed_sort_key)],
            ["a0", "a1", "b"],
        )


class RenderTests(unittest.TestCase):
    def test_no_global_sections_is_rejected(self) -> None:
        with self.assertRaises(MODULE.PlanError) as caught:
            MODULE.render([], [])
        self.assertIn("no global sections", str(caught.exception))

    def test_unknown_placeholder_is_rejected(self) -> None:
        parts = [("00-header.md", "# T\n\n<!-- plan-generated: made-up -->\n")]
        with self.assertRaises(MODULE.PlanError) as caught:
            MODULE.render(parts, [])
        self.assertIn("unknown placeholder", str(caught.exception))

    def test_repeated_placeholder_is_rejected(self) -> None:
        parts = list(MINIMAL_GLOBAL) + [
            ("30-dup.md", "<!-- plan-generated: lane-status -->\n")
        ]
        with self.assertRaises(MODULE.PlanError) as caught:
            MODULE.render(parts, [])
        self.assertIn("already used", str(caught.exception))

    def test_missing_placeholder_is_rejected(self) -> None:
        # A dropped placeholder loses every lane's contribution silently.
        parts = [
            part for part in MINIMAL_GLOBAL if "landed-changes" not in part[1]
        ]
        with self.assertRaises(MODULE.PlanError) as caught:
            MODULE.render(parts, [])
        self.assertIn("landed-changes", str(caught.exception))

    def test_first_section_must_carry_the_plan_heading(self) -> None:
        parts = [("00-header.md", "no heading here\n")] + MINIMAL_GLOBAL[1:]
        with self.assertRaises(MODULE.PlanError) as caught:
            MODULE.render(parts, [])
        self.assertIn("level-1 heading", str(caught.exception))

    def test_missing_plan_authority_marker_is_rejected(self) -> None:
        parts = [
            (name, text.replace("## Planning rules", "## House rules"))
            for name, text in MINIMAL_GLOBAL
        ]
        with self.assertRaises(MODULE.PlanError) as caught:
            MODULE.render(parts, [])
        self.assertIn("check-plan-authority", str(caught.exception))

    def test_banner_is_emitted_under_the_title(self) -> None:
        rendered = MODULE.render(MINIMAL_GLOBAL, [])
        lines = rendered.splitlines()
        self.assertEqual(lines[0], "# Axeyum plan, status, and next actions")
        self.assertIn("Generated; do not edit by hand", lines[2])

    def test_lane_blocks_land_in_order_separated_by_one_blank_line(self) -> None:
        rendered = MODULE.render(
            MINIMAL_GLOBAL,
            [
                lane({"lane-status": "**first**"}, "10-a"),
                lane({"lane-status": "**second**"}, "20-b"),
            ],
        )
        self.assertIn("**first**\n\n**second**", rendered)


class CheckModeTests(unittest.TestCase):
    def _run_check(self, contents: str) -> int:
        with TemporaryDirectory() as tmp:
            output = Path(tmp) / "PLAN.md"
            output.write_text(contents, encoding="utf-8")
            original_output, original_argv = MODULE.OUTPUT, sys.argv
            MODULE.OUTPUT = output
            sys.argv = ["gen-plan.py", "--check"]
            try:
                return MODULE.main()
            finally:
                MODULE.OUTPUT, sys.argv = original_output, original_argv

    def test_check_rejects_a_hand_edited_plan(self) -> None:
        good = MODULE.render(*MODULE.load())
        self.assertEqual(self._run_check(good), 0)
        self.assertEqual(self._run_check(good + "\nsomebody appended this\n"), 1)


class CommittedPlanTests(unittest.TestCase):
    def test_committed_plan_is_exactly_what_the_generator_produces(self) -> None:
        self.assertEqual(
            MODULE.OUTPUT.read_text(encoding="utf-8"), MODULE.render(*MODULE.load())
        )

    def test_every_lane_file_contributes_something(self) -> None:
        _, lanes = MODULE.load()
        self.assertGreater(len(lanes), 1)
        for entry in lanes:
            self.assertTrue(
                entry["sections"], f"{entry['path']} contributes no section"
            )


if __name__ == "__main__":
    unittest.main()
