#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest


SCRIPTS = pathlib.Path(__file__).parents[1]


def load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / filename)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


runner = load("fixed_authority_shadow_runner", "run-glaurung-fixed-authority-shadow-calibration.py")
analysis = load(
    "fixed_authority_shadow_analysis",
    "analyze-glaurung-fixed-authority-shadow-calibration.py",
)


class FixedAuthorityShadowCalibrationTests(unittest.TestCase):
    def test_plan_fixes_z3_and_runs_all_ten_shadow_tiers_three_times(self) -> None:
        planned = runner.planned_runs()

        self.assertEqual(len(planned), 30)
        self.assertTrue(all(row["z3_rlimit"] == 100_000 for row in planned))
        self.assertEqual(planned[0]["axeyum_progress_checks"], 8_192)
        self.assertEqual(planned[0]["bitwuzla_termination_polls"], 1)
        self.assertEqual(planned[-1]["axeyum_progress_checks"], 4_194_304)
        self.assertEqual(planned[-1]["bitwuzla_termination_polls"], 512)

    def test_shadow_selection_is_independent_and_uses_smallest_tier(self) -> None:
        tiers = [
            {
                "tier": 0,
                "limits": {
                    "axeyum_progress_checks": 8_192,
                    "bitwuzla_termination_polls": 1,
                },
                "selection_eligibility": {"axeyum": False, "bitwuzla": False},
            },
            {
                "tier": 1,
                "limits": {
                    "axeyum_progress_checks": 16_384,
                    "bitwuzla_termination_polls": 2,
                },
                "selection_eligibility": {"axeyum": False, "bitwuzla": True},
            },
            {
                "tier": 2,
                "limits": {
                    "axeyum_progress_checks": 32_768,
                    "bitwuzla_termination_polls": 4,
                },
                "selection_eligibility": {"axeyum": True, "bitwuzla": True},
            },
        ]

        selected, failures = analysis.select_shadow_limits(tiers)

        self.assertEqual(failures, [])
        self.assertEqual(selected["axeyum"]["limit"], 32_768)
        self.assertEqual(selected["bitwuzla"]["limit"], 2)

    def test_missing_shadow_limit_rejects_selection(self) -> None:
        selected, failures = analysis.select_shadow_limits(
            [
                {
                    "tier": 0,
                    "limits": {
                        "axeyum_progress_checks": 8_192,
                        "bitwuzla_termination_polls": 1,
                    },
                    "selection_eligibility": {
                        "axeyum": True,
                        "bitwuzla": False,
                    },
                }
            ]
        )

        self.assertIn("axeyum", selected)
        self.assertIn("no qualifying limit for bitwuzla", failures)


if __name__ == "__main__":
    unittest.main()
