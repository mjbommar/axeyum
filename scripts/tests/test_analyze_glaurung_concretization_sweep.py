import importlib.util
import hashlib
import unittest
from copy import deepcopy
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "analyze-glaurung-concretization-sweep.py"
SPEC = importlib.util.spec_from_file_location(
    "analyze_glaurung_concretization_sweep", SCRIPT
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


POLICIES = [
    {
        "label": "any-model",
        "policy_id": "glaurung-any-model-v1",
        "harness_choice": None,
    },
    {
        "label": "min-unsigned",
        "policy_id": "glaurung-min-unsigned-v1",
        "harness_choice": "min-unsigned",
    },
]


def text_sha256(lines: list[str]) -> str:
    return hashlib.sha256(("\n".join(lines) + "\n").encode()).hexdigest()


def registration() -> dict:
    return {
        "schema": "axeyum.glaurung-concretization-sweep-preregistration.v1",
        "name": "test-sweep",
        "glaurung_revision": "glaurung-rev",
        "source_manifest_sha256": "manifest-sha",
        "source_verified_file_count": 2,
        "authority_binary_sha256": {"z3": "z3-bin", "axeyum": "ax-bin"},
        "policies": POLICIES,
        "strata": [
            {
                "name": "positive-control",
                "kind": "validated-positive",
                "driver_sha256": ["positive-driver"],
                "coverage_boundary": "complete",
                "expected_validated_finding_count": 2,
                "work": {
                    "repetitions": 2,
                    "deadline_secs": 60,
                    "max_analyzed_functions": 100,
                    "solve_budget": 50000,
                    "solve_secs": 60,
                    "process_timeout_secs": 120,
                    "check_timeout_ms": 250,
                },
            },
            {
                "name": "tcpip-discovery",
                "kind": "unlabeled-discovery",
                "driver_sha256": ["tcpip-driver"],
                "coverage_boundary": "fixed-work-limit",
                "work": {
                    "repetitions": 2,
                    "deadline_secs": 60,
                    "max_analyzed_functions": 15,
                    "solve_budget": 50000,
                    "solve_secs": 60,
                    "process_timeout_secs": 120,
                    "check_timeout_ms": 250,
                },
            },
        ],
    }


def authority_report(
    policy: dict,
    *,
    driver_sha: str,
    boundary: str,
    raw_z3: list[str],
    raw_axeyum: list[str],
    high: list[str],
) -> dict:
    deterministic = policy["harness_choice"] is not None
    runs = []
    for repetition in (1, 2):
        for backend, raw in (("z3", raw_z3), ("axeyum", raw_axeyum)):
            diagnostic = sorted(set(raw) - set(high))
            run = {
                "backend": backend,
                "repetition": repetition,
                "finding_count": len(raw),
                "findings": raw,
                "high_confidence_finding_count": len(high),
                "high_confidence_findings": high,
                "diagnostic_finding_count": len(diagnostic),
                "diagnostic_findings": diagnostic,
                "confidence_partition_available": True,
                "coverage_boundary": boundary,
                "check_timeout_ms": 250,
                "solves": 10,
                "solver_time_ms": 2.0,
                "elapsed_seconds": 0.1,
                "max_rss_kib": 100,
            }
            run["findings_sha256"] = text_sha256(raw)
            run["high_confidence_findings_sha256"] = text_sha256(high)
            run["diagnostic_findings_sha256"] = text_sha256(diagnostic)
            run["canonical_model_choice"] = {
                "policy": policy["policy_id"],
                "attempts": 1 if deterministic else 0,
                "completed": 1 if deterministic else 0,
                "infeasible": 0,
                "probes": 2 if deterministic else 0,
                "inconclusive": 0,
                "unsupported_width": 0,
                "unknown": 0,
                "no_solver": 0,
                "error": 0,
                "final_unsat": 0,
            }
            runs.append(run)
    environment = {
        "IOCTLANCE_ALL": "1",
        "IOCTLANCE_ANNOTATE_CONFIDENCE": "1",
        "IOCTLANCE_DEADLINE_SECS": "60",
        "IOCTLANCE_SOLVE_BUDGET": "50000",
        "IOCTLANCE_SOLVE_SECS": "60",
        "IOCTLANCE_MAX_ANALYZED_FUNCTIONS": "100"
        if boundary == "complete"
        else "15",
        "GLAURUNG_CHECK_TIMEOUT_MS": "250",
    }
    if deterministic:
        environment["GLAURUNG_CONCRETIZATION_POLICY"] = policy["harness_choice"]
    exact_raw = raw_z3 == raw_axeyum
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
            "z3": {"sha256": "z3-bin"},
            "axeyum": {"sha256": "ax-bin"},
        },
        "environment": environment,
        "process_timeout_seconds": 120,
        "canonical_model_choice_required": deterministic,
        "canonical_model_choice_policy": policy["policy_id"] if deterministic else None,
        "concretization_policy_source": "preferred" if deterministic else "default",
        "concretization_policy_label": policy["harness_choice"],
        "concretization_policy_id": policy["policy_id"] if deterministic else None,
        "check_timeout_ms_required": 250,
        "acceptance_population": "high-confidence",
        "repetitions": 2,
        "order": "odd repetitions Z3/Axeyum; even repetitions Axeyum/Z3",
        "all_drivers_exact_high_confidence_finding_parity": True,
        "drivers": [
            {
                "driver": {"path": "/fixture.sys", "sha256": driver_sha},
                "summary_error": None,
                "runs": runs,
                "summary": {
                    "confidence_partition_available": True,
                    "exact_raw_finding_parity": exact_raw,
                    "exact_high_confidence_finding_parity": True,
                    "coverage": {
                        "analyzed": 1 if boundary == "complete" else 15,
                        "reachable": 1 if boundary == "complete" else 100,
                        "boundary": boundary,
                    },
                    "backends": {
                        "z3": {"solves": [10, 10]},
                        "axeyum": {"solves": [10, 10]},
                    },
                },
            }
        ],
    }


def validation(report_hash: str = "positive-hash") -> dict:
    return {
        "schema": "axeyum.glaurung-validated-finding-population.v1",
        "accepted": True,
        "validated_finding_count": 2,
        "observed_high_confidence_count": 2,
        "true_positive_count": 2,
        "false_negative_count": 0,
        "unexpected_high_confidence_count": 0,
        "recall": 1.0,
        "precision": 1.0,
        "drivers": [
            {
                "sha256": "positive-driver",
                "expected_findings": ["bug-a", "bug-b"],
                "observed_high_confidence_findings": ["bug-a", "bug-b"],
            }
        ],
        "source_verification": {
            "accepted": True,
            "verified_file_count": 2,
            "failures": [],
        },
        "inputs": {
            "manifest": {"sha256": "manifest-sha"},
            "authority_report": {"sha256": report_hash},
        },
        "failures": [],
    }


def inputs() -> tuple[dict, dict, dict]:
    reports = {}
    validations = {}
    hashes = {}
    for policy in POLICIES:
        label = policy["label"]
        positive = authority_report(
            policy,
            driver_sha="positive-driver",
            boundary="complete",
            raw_z3=["bug-a", "bug-b", "diagnostic"],
            raw_axeyum=["bug-a", "bug-b", "diagnostic"],
            high=["bug-a", "bug-b"],
        )
        discovery = authority_report(
            policy,
            driver_sha="tcpip-driver",
            boundary="fixed-work-limit",
            raw_z3=[f"{label}-shared", "z3-only"],
            raw_axeyum=[f"{label}-shared"],
            high=[],
        )
        reports[label] = {
            "positive-control": positive,
            "tcpip-discovery": discovery,
        }
        hashes[label] = {
            "positive-control": f"{label}-positive-hash",
            "tcpip-discovery": f"{label}-discovery-hash",
        }
        validations[label] = validation(hashes[label]["positive-control"])
    return reports, validations, hashes


class ConcretizationSweepAnalyzerTests(unittest.TestCase):
    def test_accepts_exact_positive_control_and_retains_unlabeled_discovery(self) -> None:
        reports, validations, hashes = inputs()
        result = MODULE.analyze_sweep(registration(), reports, validations, hashes)
        self.assertTrue(result["accepted"])
        self.assertEqual(result["positive_control"]["validated_finding_count"], 2)
        self.assertEqual(
            result["positive_control"]["policies"]["min-unsigned"][
                "true_positive_count"
            ],
            2,
        )
        discovery = result["discovery"]["tcpip-discovery"]
        self.assertEqual(discovery["policies"]["any-model"]["z3"]["raw_count"], 2)
        self.assertEqual(
            discovery["policies"]["any-model"]["axeyum"]["raw_count"], 1
        )
        self.assertIn("z3-only", discovery["raw_union"]["z3_only"])

    def test_rejects_missing_policy_or_identity_drift(self) -> None:
        reports, validations, hashes = inputs()
        reports.pop("min-unsigned")
        with self.assertRaisesRegex(RuntimeError, "policy population differs"):
            MODULE.analyze_sweep(registration(), reports, validations, hashes)

        reports, validations, hashes = inputs()
        reports["min-unsigned"]["tcpip-discovery"]["glaurung"]["revision"] = "drift"
        with self.assertRaisesRegex(RuntimeError, "Glaurung revision"):
            MODULE.analyze_sweep(registration(), reports, validations, hashes)

    def test_rejects_positive_miss_or_report_hash_mismatch(self) -> None:
        reports, validations, hashes = inputs()
        validations["min-unsigned"]["accepted"] = False
        validations["min-unsigned"]["false_negative_count"] = 1
        with self.assertRaisesRegex(RuntimeError, "positive validation was not accepted"):
            MODULE.analyze_sweep(registration(), reports, validations, hashes)

        reports, validations, hashes = inputs()
        hashes["min-unsigned"]["positive-control"] = "changed"
        with self.assertRaisesRegex(RuntimeError, "authority report hash"):
            MODULE.analyze_sweep(registration(), reports, validations, hashes)

    def test_rejects_policy_or_work_boundary_drift(self) -> None:
        reports, validations, hashes = inputs()
        reports["min-unsigned"]["tcpip-discovery"][
            "concretization_policy_id"
        ] = "other"
        with self.assertRaisesRegex(RuntimeError, "policy ID"):
            MODULE.analyze_sweep(registration(), reports, validations, hashes)

        reports, validations, hashes = inputs()
        reports["any-model"]["tcpip-discovery"]["drivers"][0]["summary"][
            "coverage"
        ]["boundary"] = "complete"
        with self.assertRaisesRegex(RuntimeError, "coverage boundary"):
            MODULE.analyze_sweep(registration(), reports, validations, hashes)

    def test_rejects_partition_hash_or_cost_corruption(self) -> None:
        reports, validations, hashes = inputs()
        runs = reports["any-model"]["tcpip-discovery"]["drivers"][0]["runs"]
        for run in runs:
            if run["backend"] == "z3":
                run["diagnostic_findings"] = []
                run["diagnostic_finding_count"] = 0
                run["diagnostic_findings_sha256"] = text_sha256([])
        with self.assertRaisesRegex(RuntimeError, "exact disjoint union"):
            MODULE.analyze_sweep(registration(), reports, validations, hashes)

        reports, validations, hashes = inputs()
        reports["any-model"]["tcpip-discovery"]["drivers"][0]["runs"][0][
            "findings_sha256"
        ] = "corrupt"
        with self.assertRaisesRegex(RuntimeError, "raw hash"):
            MODULE.analyze_sweep(registration(), reports, validations, hashes)

        reports, validations, hashes = inputs()
        reports["any-model"]["tcpip-discovery"]["drivers"][0]["runs"][0][
            "max_rss_kib"
        ] = None
        with self.assertRaisesRegex(RuntimeError, "max_rss_kib"):
            MODULE.analyze_sweep(registration(), reports, validations, hashes)


if __name__ == "__main__":
    unittest.main()
