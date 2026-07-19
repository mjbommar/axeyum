import importlib.util
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "analyze-glaurung-authority-timeout-policy.py"
SPEC = importlib.util.spec_from_file_location(
    "analyze_glaurung_authority_timeout_policy", SCRIPT
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def report(policy: str, timeout_ms: int, *, raw_parity: bool = True) -> dict:
    policy_id = (
        "glaurung-any-model-v1"
        if policy == "any-model"
        else "glaurung-min-unsigned-v1"
    )
    z3_raw = [f"shared-{timeout_ms}"]
    axeyum_raw = list(z3_raw) if raw_parity else [f"axeyum-{timeout_ms}"]
    exploration = {
        "backends": {
            "z3": {
                "runs": 20,
                "completed": 20,
                "state_budget": 0,
                "solve_budget": 0,
                "timeout_budget": 0,
                "deadline": 0,
            },
            "axeyum": {
                "runs": 20,
                "completed": 20,
                "state_budget": 0,
                "solve_budget": 0,
                "timeout_budget": 0,
                "deadline": 0,
            },
        }
    }
    environment = {
        "IOCTLANCE_ALL": "1",
        "IOCTLANCE_ANNOTATE_CONFIDENCE": "1",
        "IOCTLANCE_DEADLINE_SECS": "2400",
        "IOCTLANCE_SOLVE_BUDGET": "400000",
        "IOCTLANCE_SOLVE_SECS": "900",
        "IOCTLANCE_MAX_ANALYZED_FUNCTIONS": "20",
        "GLAURUNG_CHECK_TIMEOUT_MS": str(timeout_ms),
    }
    if policy == "min-unsigned":
        environment["GLAURUNG_CONCRETIZATION_POLICY"] = "min-unsigned"
    return {
        "schema": "axeyum.glaurung-authoritative-finding-parity.v6",
        "accepted": True,
        "failures": [],
        "glaurung": {
            "revision": MODULE.EXPECTED_GLAURUNG_REVISION,
            "tracked_dirty": False,
        },
        "axeyum": {"revision": "axeyum-rev", "tracked_dirty": False},
        "post_run_source_identity": {"stable": True},
        "binaries": {
            "z3": {"sha256": MODULE.EXPECTED_Z3_BINARY_SHA256},
            "axeyum": {"sha256": MODULE.EXPECTED_AXEYUM_BINARY_SHA256},
        },
        "environment": environment,
        "process_timeout_seconds": 2700,
        "canonical_model_choice_required": policy == "min-unsigned",
        "canonical_model_choice_policy": (
            policy_id if policy == "min-unsigned" else None
        ),
        "concretization_policy_source": (
            "preferred" if policy == "min-unsigned" else "default"
        ),
        "concretization_policy_label": (
            "min-unsigned" if policy == "min-unsigned" else None
        ),
        "concretization_policy_id": (
            policy_id if policy == "min-unsigned" else None
        ),
        "check_timeout_ms_required": timeout_ms,
        "deterministic_worklists_required": True,
        "acceptance_population": "high-confidence",
        "repetitions": 3,
        "order": "odd repetitions Z3/Axeyum; even repetitions Axeyum/Z3",
        "drivers": [
            {
                "driver": {
                    "path": "/tcpip.sys",
                    "sha256": MODULE.EXPECTED_DRIVER_SHA256,
                },
                "summary_error": None,
                "summary": {
                    "within_backend_stable": True,
                    "exact_raw_finding_parity": raw_parity,
                    "exact_high_confidence_finding_parity": True,
                    "raw": {
                        "z3_only": sorted(set(z3_raw) - set(axeyum_raw)),
                        "axeyum_only": sorted(set(axeyum_raw) - set(z3_raw)),
                    },
                    "high_confidence": {"z3_only": [], "axeyum_only": []},
                    "coverage": {
                        "analyzed": 20,
                        "reachable": 338,
                        "boundary": "fixed-work-limit",
                    },
                    "check_timeout_ms": timeout_ms,
                    "deterministic_worklists_verified": True,
                    "exploration_limits": exploration,
                    "canonical_model_choice": {
                        "policy": policy_id,
                        "backends": {
                            "z3": {"policy": policy_id, "inconclusive": 0},
                            "axeyum": {"policy": policy_id, "inconclusive": 0},
                        },
                    },
                    "backends": {
                        "z3": {
                            "finding_count": len(z3_raw),
                            "high_confidence_finding_count": 0,
                            "solves": [100, 100, 100],
                            "elapsed_seconds": [1.0, 1.1, 1.0],
                            "max_rss_kib": [10, 10, 10],
                        },
                        "axeyum": {
                            "finding_count": len(axeyum_raw),
                            "high_confidence_finding_count": 0,
                            "solves": [90, 90, 90],
                            "elapsed_seconds": [0.8, 0.9, 0.8],
                            "max_rss_kib": [9, 9, 9],
                        },
                    },
                },
            }
        ],
    }


def matrix() -> dict[tuple[str, int], dict]:
    return {
        (policy, timeout): report(
            policy,
            timeout,
            raw_parity=not (policy == "any-model" and timeout == 250),
        )
        for policy in MODULE.POLICIES
        for timeout in MODULE.TIMEOUTS_MS
    }


class AuthorityTimeoutPolicyTests(unittest.TestCase):
    def test_accepts_complete_matrix_and_reports_hypothesis_separately(self) -> None:
        analyzed = MODULE.analyze_reports(matrix(), "axeyum-rev")
        self.assertTrue(analyzed["valid"])
        self.assertFalse(analyzed["any_model_raw_parity_all_timeouts"])
        self.assertTrue(analyzed["least_unsigned_raw_parity_all_timeouts"])
        self.assertEqual(len(analyzed["cells"]), 6)

    def test_rejects_missing_cell(self) -> None:
        reports = matrix()
        del reports[("min-unsigned", 1000)]
        with self.assertRaisesRegex(RuntimeError, "matrix is incomplete"):
            MODULE.analyze_reports(reports, "axeyum-rev")

    def test_rejects_legacy_schema(self) -> None:
        reports = matrix()
        reports[("any-model", 100)]["schema"] = (
            "axeyum.glaurung-authoritative-finding-parity.v5"
        )
        with self.assertRaisesRegex(RuntimeError, "schema mismatch"):
            MODULE.analyze_reports(reports, "axeyum-rev")

    def test_rejects_hidden_timeout_stop(self) -> None:
        reports = matrix()
        summary = reports[("min-unsigned", 250)]["drivers"][0]["summary"]
        z3 = summary["exploration_limits"]["backends"]["z3"]
        z3["completed"] = 19
        z3["timeout_budget"] = 1
        with self.assertRaisesRegex(RuntimeError, "deadline/timeout worklist stop"):
            MODULE.analyze_reports(reports, "axeyum-rev")

    def test_rejects_source_drift(self) -> None:
        reports = matrix()
        reports[("min-unsigned", 1000)]["axeyum"]["revision"] = "drift"
        with self.assertRaisesRegex(RuntimeError, "Axeyum revision mismatch"):
            MODULE.analyze_reports(reports, "axeyum-rev")


if __name__ == "__main__":
    unittest.main()
