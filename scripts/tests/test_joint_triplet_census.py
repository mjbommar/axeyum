#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import json
import pathlib
import sys
import tempfile
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "run-glaurung-joint-triplet-census.py"
SPEC = importlib.util.spec_from_file_location("joint_triplet_runner", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
runner = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = runner
SPEC.loader.exec_module(runner)


class JointTripletCensusTests(unittest.TestCase):
    def test_each_phase_has_three_exact_triplet_processes(self) -> None:
        runner.configure_phase("phase-a")
        planned = runner.BASE.planned_runs()

        self.assertEqual(len(planned), 3)
        self.assertTrue(
            all(
                (
                    row["z3_rlimit"],
                    row["axeyum_progress_checks"],
                    row["bitwuzla_termination_polls"],
                )
                == runner.TRIPLET
                for row in planned
            )
        )
        self.assertEqual(
            runner.BASE.FIXED_ENVIRONMENT["IOCTLANCE_MAX_ANALYZED_FUNCTIONS"],
            "20",
        )
        runner.configure_phase("phase-b")
        self.assertEqual(
            runner.BASE.FIXED_ENVIRONMENT["IOCTLANCE_MAX_ANALYZED_FUNCTIONS"],
            "338",
        )

    def test_phase_b_requires_accepted_unchanged_phase_a(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            phase_a = root / "phase-a"
            phase_a.mkdir()
            campaign = phase_a / "campaign.json"
            campaign.write_text("{}\n", encoding="utf-8")
            report = root / "phase-a-analysis.json"
            report.write_text(
                json.dumps(
                    {
                        "schema": "axeyum-glaurung-adr0275-phase-a-analysis-v1",
                        "phase": "phase-a",
                        "accepted": True,
                        "campaign_sha256": runner.BASE.sha256_file(campaign),
                        "triplet": {
                            "z3_rlimit": runner.TRIPLET[0],
                            "axeyum_progress_checks": runner.TRIPLET[1],
                            "bitwuzla_termination_polls": runner.TRIPLET[2],
                        },
                    }
                ),
                encoding="utf-8",
            )

            runner.require_phase_a(root)
            campaign.write_text('{"changed": true}\n', encoding="utf-8")
            with self.assertRaisesRegex(runner.BASE.CampaignError, "changed"):
                runner.require_phase_a(root)


if __name__ == "__main__":
    unittest.main()
