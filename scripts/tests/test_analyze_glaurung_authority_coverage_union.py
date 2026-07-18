import importlib.util
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "analyze-glaurung-authority-coverage-union.py"
SPEC = importlib.util.spec_from_file_location(
    "analyze_glaurung_authority_coverage_union", SCRIPT
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def report(
    policy: str | None,
    z3_findings: list[str],
    axeyum_findings: list[str] | None = None,
) -> dict:
    axeyum_findings = z3_findings if axeyum_findings is None else axeyum_findings
    environment = {
        "IOCTLANCE_ALL": "1",
        "IOCTLANCE_DEADLINE_SECS": "1800",
        "IOCTLANCE_MAX_ANALYZED_FUNCTIONS": "15",
        "IOCTLANCE_SOLVE_BUDGET": "300000",
        "IOCTLANCE_SOLVE_SECS": "300",
        "GLAURUNG_CHECK_TIMEOUT_MS": "250",
    }
    policy_name = None
    if policy is not None:
        environment["GLAURUNG_CANONICAL_MODEL_CHOICE"] = policy
        policy_name = f"glaurung-{policy}-v1"
    runs = []
    for repetition in range(1, 4):
        for backend, findings in (
            ("z3", z3_findings),
            ("axeyum", axeyum_findings),
        ):
            run = {
                "backend": backend,
                "repetition": repetition,
                "position": 1,
                "findings": findings,
                "finding_count": len(findings),
                "analyzed": 15,
                "analysis_roots": 338,
                "coverage_boundary": "fixed-work-limit",
                "solves": 100,
            }
            if policy_name is not None:
                run["canonical_model_choice"] = {
                    "policy": policy_name,
                    "attempts": 2,
                    "completed": 2,
                    "infeasible": 0,
                    "probes": 132,
                    "inconclusive": 0,
                    "unsupported_width": 0,
                    "unknown": 0,
                    "no_solver": 0,
                    "error": 0,
                    "final_unsat": 0,
                }
            runs.append(run)
    exact = z3_findings == axeyum_findings
    return {
        "schema": "axeyum.glaurung-authoritative-finding-parity.v4",
        "accepted": exact,
        "failures": [] if exact else ["expected baseline divergence"],
        "glaurung": {"revision": "glaurung-rev", "tracked_dirty": False},
        "axeyum": {"revision": "axeyum-rev", "tracked_dirty": False},
        "post_run_source_identity": {"stable": True},
        "binaries": {
            "z3": {"sha256": "z3-bin"},
            "axeyum": {"sha256": "axeyum-bin"},
        },
        "environment": environment,
        "process_timeout_seconds": 1800,
        "canonical_model_choice_required": policy is not None,
        "canonical_model_choice_policy": policy_name,
        "check_timeout_ms_required": 250,
        "repetitions": 3,
        "order": "balanced",
        "all_drivers_exact_finding_parity": exact,
        "drivers": [
            {
                "driver": {"path": "/tcpip.sys", "sha256": "driver-sha"},
                "runs": runs,
                "summary": {
                    "exact_finding_parity": exact,
                    "within_backend_stable": True,
                    "coverage": {
                        "analyzed": 15,
                        "reachable": 338,
                        "boundary": "fixed-work-limit",
                    },
                    "canonical_model_choice": (
                        {
                            "policy": policy_name,
                            "backends": {
                                "z3": runs[0]["canonical_model_choice"],
                                "axeyum": runs[1]["canonical_model_choice"],
                            },
                        }
                        if policy_name is not None
                        else None
                    ),
                    "backends": {
                        "z3": {"solves": [100, 100, 100]},
                        "axeyum": {"solves": [100, 100, 100]},
                    },
                },
                "summary_error": None,
            }
        ],
    }


class AuthorityCoverageUnionTests(unittest.TestCase):
    def test_accepts_stable_two_policy_union_with_rejected_any_baseline(self) -> None:
        analyzed = MODULE.analyze_reports(
            report(None, ["a", "z3-only"], ["a"]),
            report("min-unsigned", ["a", "min-only"]),
            report("max-unsigned", ["a", "max-only"]),
        )
        self.assertTrue(analyzed["accepted"])
        self.assertEqual(
            analyzed["coverage_union"]["ordered_findings"],
            ["a", "max-only", "min-only"],
        )
        self.assertTrue(analyzed["coverage_union"]["exact_authority_parity"])
        self.assertEqual(analyzed["any_model_baseline"]["z3_only"], ["z3-only"])

    def test_rejects_policy_level_authority_divergence(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "max-unsigned authority findings differ"):
            MODULE.analyze_reports(
                report(None, ["a", "z3-only"], ["a"]),
                report("min-unsigned", ["a"]),
                report("max-unsigned", ["a"], ["b"]),
            )

    def test_rejects_cross_cell_source_drift(self) -> None:
        maximum = report("max-unsigned", ["a"])
        maximum["glaurung"]["revision"] = "different"
        with self.assertRaisesRegex(RuntimeError, "glaurung identity drift"):
            MODULE.analyze_reports(
                report(None, ["a", "z3-only"], ["a"]),
                report("min-unsigned", ["a"]),
                maximum,
            )

    def test_rejects_an_accepted_any_model_baseline(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "must preserve a stable divergence"):
            MODULE.analyze_reports(
                report(None, ["a"]),
                report("min-unsigned", ["a"]),
                report("max-unsigned", ["a"]),
            )


if __name__ == "__main__":
    unittest.main()
