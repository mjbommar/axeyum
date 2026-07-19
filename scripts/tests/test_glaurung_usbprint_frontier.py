from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path


RUNNER_PATH = Path(__file__).parents[1] / "run-glaurung-usbprint-frontier.py"
RUNNER_SPEC = importlib.util.spec_from_file_location("usbprint_frontier_runner", RUNNER_PATH)
assert RUNNER_SPEC and RUNNER_SPEC.loader
RUNNER = importlib.util.module_from_spec(RUNNER_SPEC)
RUNNER_SPEC.loader.exec_module(RUNNER)

ANALYZER_PATH = Path(__file__).parents[1] / "analyze-glaurung-usbprint-frontier.py"
ANALYZER_SPEC = importlib.util.spec_from_file_location(
    "usbprint_frontier_analyzer", ANALYZER_PATH
)
assert ANALYZER_SPEC and ANALYZER_SPEC.loader
ANALYZER = importlib.util.module_from_spec(ANALYZER_SPEC)
ANALYZER_SPEC.loader.exec_module(ANALYZER)


POLICIES = [
    ("any-model", "glaurung-any-model-v1", None),
    ("min-unsigned", "glaurung-min-unsigned-v1", "min-unsigned"),
    ("max-unsigned", "glaurung-max-unsigned-v1", "max-unsigned"),
    ("site-hash-0", "glaurung-site-hash-0-v1", "site-hash-0"),
    ("site-hash-1", "glaurung-site-hash-1-v1", "site-hash-1"),
]


def registration() -> dict:
    return {
        "schema": RUNNER.REGISTRATION_SCHEMA,
        "name": "usbprint-frontier-v1",
        "glaurung_revision": "glaurung-rev",
        "authority_binary_sha256": {"z3": "z3-sha", "axeyum": "ax-sha"},
        "driver": {"sha256": "driver-sha"},
        "policies": [
            {
                "label": label,
                "policy_id": policy_id,
                "harness_choice": choice,
            }
            for label, policy_id, choice in POLICIES
        ],
        "points": [
            {
                "label": f"prefix-{limit}",
                "max_analyzed_functions": limit,
                "work": {
                    "repetitions": 2,
                    "deadline_secs": 1800,
                    "solve_budget": 300000,
                    "solve_secs": 300,
                    "process_timeout_secs": 1920,
                    "check_timeout_ms": 250,
                },
            }
            for limit in (5, 10, 15)
        ],
        "acceptance": {"population": "high-confidence"},
        "claim_limits": ["bounded resource result"],
    }


def accepted_report(policy_id: str, limit: int, solves: int = 10) -> dict:
    runs = []
    for repetition, order in ((1, ("z3", "axeyum")), (2, ("axeyum", "z3"))):
        for position, backend in enumerate(order, start=1):
            runs.append(
                {
                    "backend": backend,
                    "repetition": repetition,
                    "position": position,
                    "analyzed": limit,
                    "analysis_roots": 21,
                    "coverage_boundary": "fixed-work-limit",
                    "check_timeout_ms": 250,
                    "solves": solves,
                    "elapsed_seconds": 1.0,
                    "max_rss_kib": 100,
                    "finding_count": 3,
                    "high_confidence_finding_count": 0,
                    "diagnostic_finding_count": 3,
                    "canonical_model_choice": {"policy": policy_id},
                }
            )
    return {
        "schema": "axeyum.glaurung-authoritative-finding-parity.v5",
        "accepted": True,
        "failures": [],
        "glaurung": {"revision": "glaurung-rev", "tracked_dirty": False},
        "axeyum": {"revision": "axeyum-rev", "tracked_dirty": False},
        "post_run_source_identity": {
            "stable": True,
            "glaurung": {"revision": "glaurung-rev", "tracked_dirty": False},
            "axeyum": {"revision": "axeyum-rev", "tracked_dirty": False},
        },
        "binaries": {
            "z3": {"sha256": "z3-sha"},
            "axeyum": {"sha256": "ax-sha"},
        },
        "environment": {
            "IOCTLANCE_DEADLINE_SECS": "1800",
            "IOCTLANCE_MAX_ANALYZED_FUNCTIONS": str(limit),
            "IOCTLANCE_SOLVE_BUDGET": "300000",
            "IOCTLANCE_SOLVE_SECS": "300",
            "GLAURUNG_CHECK_TIMEOUT_MS": "250",
        },
        "process_timeout_seconds": 1920,
        "repetitions": 2,
        "acceptance_population": "high-confidence",
        "concretization_policy_id": (
            None if policy_id == "glaurung-any-model-v1" else policy_id
        ),
        "concretization_policy_source": (
            "default" if policy_id == "glaurung-any-model-v1" else "preferred"
        ),
        "all_drivers_exact_high_confidence_finding_parity": True,
        "drivers": [
            {
                "driver": {"sha256": "driver-sha"},
                "summary_error": None,
                "summary": {
                    "coverage": {
                        "analyzed": limit,
                        "reachable": 21,
                        "boundary": "fixed-work-limit",
                    },
                    "confidence_partition_available": True,
                    "high_confidence": {
                        "exact_finding_parity": True,
                        "stability": {
                            "z3": {"output_stable": True},
                            "axeyum": {"output_stable": True},
                        },
                    },
                    "backends": {
                        "z3": {"high_confidence_finding_count": 0},
                        "axeyum": {"high_confidence_finding_count": 0},
                    },
                },
                "runs": runs,
            }
        ],
    }


def resource_report(policy_id: str, limit: int) -> dict:
    result = accepted_report(policy_id, limit)
    result["accepted"] = False
    result["failures"] = ["driver: process failures"]
    result["all_drivers_exact_high_confidence_finding_parity"] = False
    result["drivers"][0]["summary"] = None
    result["drivers"][0]["summary_error"] = "process failures"
    result["drivers"][0]["runs"] = [
        {
            "backend": backend,
            "repetition": repetition,
            "position": position,
            "run_error": "analysis hit the wall-clock safety deadline",
        }
        for repetition, order in ((1, ("z3", "axeyum")), (2, ("axeyum", "z3")))
        for position, backend in enumerate(order, start=1)
    ]
    return result


def execution(reports: dict[tuple[str, str], dict], stop: tuple[str, str] | None = None) -> dict:
    cells = []
    for point in ("prefix-5", "prefix-10", "prefix-15"):
        for policy, _, _ in POLICIES:
            key = (point, policy)
            if key not in reports:
                continue
            report = reports[key]
            classification = RUNNER.classify_report(report)
            cells.append(
                {
                    "point": point,
                    "policy": policy,
                    "report_sha256": f"sha-{point}-{policy}",
                    "classification": classification,
                    "returncode": 0 if classification == "complete" else 1,
                }
            )
            if stop == key:
                break
        if stop is not None and cells and (cells[-1]["point"], cells[-1]["policy"]) == stop:
            break
    return {
        "schema": RUNNER.EXECUTION_SCHEMA,
        "registration_sha256": "registration-sha",
        "glaurung": {"revision": "glaurung-rev", "tracked_dirty": False},
        "axeyum": {"revision": "axeyum-rev", "tracked_dirty": False},
        "source_identity_stable": True,
        "cells": cells,
    }


class UsbprintFrontierTests(unittest.TestCase):
    def test_registration_and_command_fix_point_major_frontier(self) -> None:
        candidate = registration()
        RUNNER.validate_registration(candidate)
        self.assertEqual(RUNNER.cell_order(candidate)[0], ("prefix-5", "any-model"))
        self.assertEqual(RUNNER.cell_order(candidate)[-1], ("prefix-15", "site-hash-1"))
        command = RUNNER.measure_command(
            python_executable="python",
            measure_script=Path("measure.py"),
            glaurung_repo=Path("glaurung"),
            z3_binary=Path("z3-bin"),
            axeyum_binary=Path("ax-bin"),
            driver=Path("usbprint.sys"),
            policy=candidate["policies"][1],
            point=candidate["points"][2],
            out=Path("report.json"),
        )
        self.assertIn("--max-analyzed-functions", command)
        self.assertIn("15", command)
        self.assertIn("--concretization-policy", command)
        self.assertIn("min-unsigned", command)

    def test_registration_rejects_point_or_policy_drift(self) -> None:
        bad_point = registration()
        bad_point["points"][1]["max_analyzed_functions"] = 11
        with self.assertRaisesRegex(RuntimeError, "frontier points differ"):
            RUNNER.validate_registration(bad_point)
        bad_policy = registration()
        bad_policy["policies"].reverse()
        with self.assertRaisesRegex(RuntimeError, "policy order"):
            RUNNER.validate_registration(bad_policy)

    def test_report_classification_is_fail_closed(self) -> None:
        self.assertEqual(
            RUNNER.classify_report(accepted_report("glaurung-any-model-v1", 5)),
            "complete",
        )
        self.assertEqual(
            RUNNER.classify_report(resource_report("glaurung-min-unsigned-v1", 15)),
            "resource-bound",
        )
        corrupt = resource_report("glaurung-min-unsigned-v1", 15)
        corrupt["drivers"][0]["runs"][0]["run_error"] = "parse failed"
        self.assertEqual(RUNNER.classify_report(corrupt), "protocol-failure")

    def test_analyzer_accepts_complete_matrix_and_common_prefix(self) -> None:
        reports = {
            (f"prefix-{limit}", policy): accepted_report(policy_id, limit)
            for limit in (5, 10, 15)
            for policy, policy_id, _ in POLICIES
        }
        result = ANALYZER.analyze_frontier(
            registration(),
            execution(reports),
            reports,
            registration_sha256="registration-sha",
            report_hashes={key: f"sha-{key[0]}-{key[1]}" for key in reports},
        )
        self.assertTrue(result["accepted"])
        self.assertTrue(result["matrix_complete"])
        self.assertEqual(result["common_completed_prefix"], 15)
        self.assertEqual(result["high_confidence_finding_count"], 0)

    def test_analyzer_accepts_pure_resource_bracket_after_complete_lower_points(self) -> None:
        reports = {
            (f"prefix-{limit}", policy): accepted_report(policy_id, limit)
            for limit in (5, 10)
            for policy, policy_id, _ in POLICIES
        }
        reports[("prefix-15", "any-model")] = accepted_report(
            "glaurung-any-model-v1", 15
        )
        reports[("prefix-15", "min-unsigned")] = resource_report(
            "glaurung-min-unsigned-v1", 15
        )
        result = ANALYZER.analyze_frontier(
            registration(),
            execution(reports, stop=("prefix-15", "min-unsigned")),
            reports,
            registration_sha256="registration-sha",
            report_hashes={key: f"sha-{key[0]}-{key[1]}" for key in reports},
        )
        self.assertTrue(result["accepted"])
        self.assertFalse(result["matrix_complete"])
        self.assertEqual(result["common_completed_prefix"], 10)
        self.assertEqual(result["first_resource_bound"], ["prefix-15", "min-unsigned"])

    def test_analyzer_rejects_hash_or_lower_prefix_failure(self) -> None:
        reports = {
            ("prefix-5", "any-model"): resource_report("glaurung-any-model-v1", 5)
        }
        result = ANALYZER.analyze_frontier(
            registration(),
            execution(reports, stop=("prefix-5", "any-model")),
            reports,
            registration_sha256="registration-sha",
            report_hashes={("prefix-5", "any-model"): "wrong"},
        )
        self.assertFalse(result["accepted"])
        self.assertTrue(any("no complete common prefix" in row for row in result["failures"]))
        self.assertTrue(any("report SHA-256" in row for row in result["failures"]))


if __name__ == "__main__":
    unittest.main()
