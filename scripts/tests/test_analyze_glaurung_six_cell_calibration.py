#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "analyze-glaurung-six-cell-calibration.py"
SPEC = importlib.util.spec_from_file_location("six_cell_calibration_analysis", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
analysis = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = analysis
SPEC.loader.exec_module(analysis)


def tier(
    index: int,
    *,
    z3: bool = False,
    axeyum: bool = False,
    bitwuzla: bool = False,
) -> dict[str, object]:
    return {
        "tier": index,
        "limits": {
            "z3_rlimit": 10 + index,
            "axeyum_progress_checks": 20 + index,
            "bitwuzla_termination_polls": 30 + index,
        },
        "selection_eligibility": {
            "z3": z3,
            "axeyum": axeyum,
            "bitwuzla": bitwuzla,
        },
    }


class SixCellCalibrationAnalysisTests(unittest.TestCase):
    def test_selects_each_backend_independently_at_its_smallest_eligible_tier(self) -> None:
        tiers = [
            tier(0, z3=True),
            tier(1, z3=True, axeyum=True),
            tier(2, z3=True, axeyum=True, bitwuzla=True),
            tier(3, z3=True, axeyum=True, bitwuzla=True),
        ]

        selected, failures = analysis.select_limits(tiers)

        self.assertEqual(failures, [])
        self.assertEqual(
            selected,
            {
                "z3": {"tier": 0, "unit": "z3-rlimit", "limit": 10},
                "axeyum": {
                    "tier": 1,
                    "unit": "axeyum-progress-checks",
                    "limit": 21,
                },
                "bitwuzla": {
                    "tier": 2,
                    "unit": "bitwuzla-termination-polls",
                    "limit": 32,
                },
            },
        )

    def test_missing_eligible_backend_rejects_selection(self) -> None:
        selected, failures = analysis.select_limits([tier(0, z3=True, axeyum=True)])

        self.assertNotIn("bitwuzla", selected)
        self.assertIn("no qualifying limit for bitwuzla", failures)

    def test_parses_fixed_prefix_and_rejects_hidden_wall_stops(self) -> None:
        stderr = """
[symbolic] 1.2s raw=3 high-confidence=1 suppressed=2 (ArgN pointer-deref noise) analyzed=20/338 WORK-LIMIT-HIT (fixed reachable-function prefix complete)
[finding-confidence] schema=glaurung-ioctlance-confidence-v1 high=1 diagnostic=2
[exploration-limits] runs=21 completed=20 state_budget=1 solve_budget=0 timeout_budget=0 deadline=0
"""
        parsed = analysis.parse_stderr(stderr)
        self.assertEqual(parsed["coverage"], {"analyzed": 20, "reachable": 338})
        self.assertEqual(parsed["exploration_limits"]["state_budget"], 1)

        with self.assertRaisesRegex(analysis.CalibrationError, "timeout/deadline"):
            analysis.parse_stderr(stderr.replace("timeout_budget=0", "timeout_budget=1"))


if __name__ == "__main__":
    unittest.main()
