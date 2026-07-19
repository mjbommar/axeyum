import importlib.util
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "measure-glaurung-authoritative-findings.py"
SPEC = importlib.util.spec_from_file_location(
    "measure_glaurung_authoritative_findings", SCRIPT
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def run(
    backend: str, *, analyzed: int = 10, boundary: str = "fixed-work-limit"
) -> dict:
    findings = ["sink-a"]
    return {
        "backend": backend,
        "finding_count": 1,
        "findings_sha256": "hash",
        "findings": findings,
        "reported_raw": 1,
        "reported_lines": 1,
        "reported_high_confidence": 1,
        "reported_suppressed": 0,
        "confidence_partition_available": True,
        "finding_confidence_schema": MODULE.FINDING_CONFIDENCE_SCHEMA,
        "high_confidence_finding_count": 1,
        "high_confidence_findings_sha256": "hash",
        "high_confidence_findings": findings,
        "diagnostic_finding_count": 0,
        "diagnostic_findings_sha256": MODULE.text_sha256([]),
        "diagnostic_findings": [],
        "analyzed": analyzed,
        "analysis_roots": 100,
        "coverage_boundary": boundary,
        "solves": 1,
        "solver_time_ms": 1.0,
        "average_us_per_solve": 1000.0,
        "elapsed_seconds": 1.0,
        "max_rss_kib": 100,
        "time_exit": 0,
    }


class AuthoritativeFindingRunnerTests(unittest.TestCase):
    def test_parses_machine_readable_confidence_partition_without_changing_rows(
        self,
    ) -> None:
        parsed = MODULE.parse_annotated_findings(
            "sink-a\tconfidence=high\nsink-b\tconfidence=diagnostic\n"
        )
        self.assertEqual(parsed["findings"], ["sink-a", "sink-b"])
        self.assertEqual(parsed["high_confidence_findings"], ["sink-a"])
        self.assertEqual(parsed["diagnostic_findings"], ["sink-b"])
        self.assertTrue(parsed["confidence_partition_available"])

    def test_preserves_legacy_raw_output_but_rejects_mixed_or_unknown_annotations(
        self,
    ) -> None:
        empty = MODULE.parse_annotated_findings("", annotation_active=True)
        self.assertTrue(empty["confidence_partition_available"])
        self.assertEqual(empty["high_confidence_findings"], [])
        self.assertEqual(empty["diagnostic_findings"], [])
        parsed = MODULE.parse_annotated_findings("sink-a\nsink-b\n")
        self.assertEqual(parsed["findings"], ["sink-a", "sink-b"])
        self.assertFalse(parsed["confidence_partition_available"])
        with self.assertRaisesRegex(RuntimeError, "mixed annotated and legacy"):
            MODULE.parse_annotated_findings("sink-a\tconfidence=high\nsink-b\n")
        with self.assertRaisesRegex(RuntimeError, "unknown finding confidence"):
            MODULE.parse_annotated_findings("sink-a\tconfidence=review-me\n")

    def test_accepts_and_verifies_reported_check_timeout(self) -> None:
        stderr = (
            "[solver] backend=z3 solves=10 solver_time=2.0ms "
            "avg=200.0us/solve check_timeout_ms=1000\n"
        )
        self.assertEqual(MODULE.parse_check_timeout_ms(stderr, expected=1000), 1000)
        with self.assertRaisesRegex(RuntimeError, "check-timeout mismatch"):
            MODULE.parse_check_timeout_ms(stderr, expected=2000)
        with self.assertRaisesRegex(RuntimeError, "missing solver check-timeout"):
            MODULE.parse_check_timeout_ms("", expected=1000)

    def test_accepts_complete_canonical_model_choice_footer(self) -> None:
        telemetry = MODULE.parse_canonical_model_choice(
            "[canonical-model-choice] policy=glaurung-min-unsigned-v1 "
            "attempts=7 completed=5 infeasible=2 probes=332 inconclusive=0 "
            "unsupported_width=0 unknown=0 no_solver=0 error=0 final_unsat=0\n",
            required_policy="glaurung-min-unsigned-v1",
        )
        self.assertEqual(
            telemetry,
            {
                "policy": "glaurung-min-unsigned-v1",
                "attempts": 7,
                "completed": 5,
                "infeasible": 2,
                "probes": 332,
                "inconclusive": 0,
                "unsupported_width": 0,
                "unknown": 0,
                "no_solver": 0,
                "error": 0,
                "final_unsat": 0,
            },
        )

    def test_accepts_explicit_maximum_canonical_model_policy(self) -> None:
        telemetry = MODULE.parse_canonical_model_choice(
            "[canonical-model-choice] policy=glaurung-max-unsigned-v1 "
            "attempts=4 completed=4 infeasible=0 probes=264 inconclusive=0 "
            "unsupported_width=0 unknown=0 no_solver=0 error=0 final_unsat=0\n",
            required_policy="glaurung-max-unsigned-v1",
        )
        self.assertEqual(telemetry["policy"], "glaurung-max-unsigned-v1")

    def test_exposes_complementary_site_hash_canonical_model_policies(self) -> None:
        self.assertEqual(
            MODULE.CANONICAL_MODEL_POLICIES["site-hash-0"],
            "glaurung-site-hash-0-v1",
        )
        self.assertEqual(
            MODULE.CANONICAL_MODEL_POLICIES["site-hash-1"],
            "glaurung-site-hash-1-v1",
        )

    def test_prefers_first_class_concretization_policy_configuration(self) -> None:
        preferred = MODULE.resolve_policy_configuration("site-hash-0", None)
        self.assertEqual(
            preferred,
            {
                "environment": {
                    "GLAURUNG_CONCRETIZATION_POLICY": "site-hash-0"
                },
                "label": "site-hash-0",
                "policy_id": "glaurung-site-hash-0-v1",
                "source": "preferred",
            },
        )
        legacy = MODULE.resolve_policy_configuration(None, "max-unsigned")
        self.assertEqual(
            legacy["environment"],
            {"GLAURUNG_CANONICAL_MODEL_CHOICE": "max-unsigned"},
        )
        self.assertEqual(legacy["source"], "legacy")
        self.assertEqual(
            MODULE.resolve_policy_configuration(None, None),
            {
                "environment": {},
                "label": None,
                "policy_id": None,
                "source": "default",
            },
        )
        with self.assertRaisesRegex(RuntimeError, "configure exactly one"):
            MODULE.resolve_policy_configuration("min-unsigned", "max-unsigned")

    def test_rejects_missing_or_unexercised_canonical_model_choice(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "missing canonical-model-choice"):
            MODULE.parse_canonical_model_choice(
                "", required_policy="glaurung-min-unsigned-v1"
            )
        with self.assertRaisesRegex(RuntimeError, "was not exercised"):
            MODULE.parse_canonical_model_choice(
                "[canonical-model-choice] policy=glaurung-min-unsigned-v1 "
                "attempts=0 completed=0 infeasible=0 probes=0 inconclusive=0 "
                "unsupported_width=0 unknown=0 no_solver=0 error=0 final_unsat=0\n",
                required_policy="glaurung-min-unsigned-v1",
            )

    def test_rejects_wrong_or_inconclusive_canonical_model_choice(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "unexpected canonical model policy"):
            MODULE.parse_canonical_model_choice(
                "[canonical-model-choice] policy=glaurung-any-model-v1 "
                "attempts=1 completed=1 infeasible=0 probes=2 inconclusive=0 "
                "unsupported_width=0 unknown=0 no_solver=0 error=0 final_unsat=0\n",
                required_policy="glaurung-min-unsigned-v1",
            )
        with self.assertRaisesRegex(RuntimeError, "did not complete every attempt"):
            MODULE.parse_canonical_model_choice(
                "[canonical-model-choice] policy=glaurung-min-unsigned-v1 "
                "attempts=2 completed=1 infeasible=0 probes=65 inconclusive=1 "
                "unsupported_width=0 unknown=1 no_solver=0 error=0 final_unsat=0\n",
                required_policy="glaurung-min-unsigned-v1",
            )

    def test_accepts_exact_declared_fixed_work_boundary(self) -> None:
        boundary = MODULE.validate_coverage_boundary(
            tail=" WORK-LIMIT-HIT (fixed reachable-function prefix complete)",
            analyzed=10,
            reachable=100,
            max_analyzed_functions=10,
        )
        self.assertEqual(boundary, "fixed-work-limit")

    def test_rejects_deadline_even_with_fixed_work_configured(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "safety deadline"):
            MODULE.validate_coverage_boundary(
                tail=" DEADLINE-HIT",
                analyzed=9,
                reachable=100,
                max_analyzed_functions=10,
            )

    def test_rejects_undeclared_or_mismatched_fixed_work_boundary(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "undeclared"):
            MODULE.validate_coverage_boundary(
                tail=" WORK-LIMIT-HIT",
                analyzed=10,
                reachable=100,
                max_analyzed_functions=None,
            )
        with self.assertRaisesRegex(RuntimeError, "count mismatch"):
            MODULE.validate_coverage_boundary(
                tail=" WORK-LIMIT-HIT",
                analyzed=9,
                reachable=100,
                max_analyzed_functions=10,
            )

    def test_accepts_complete_population_below_optional_ceiling(self) -> None:
        boundary = MODULE.validate_coverage_boundary(
            tail="",
            analyzed=8,
            reachable=8,
            max_analyzed_functions=10,
        )
        self.assertEqual(boundary, "complete")

    def test_rejects_cross_authority_coverage_drift(self) -> None:
        runs = [
            run("z3"),
            run("z3"),
            run("axeyum", analyzed=9),
            run("axeyum", analyzed=9),
        ]
        with self.assertRaisesRegex(
            RuntimeError, "authority coverage populations differ"
        ):
            MODULE.summarize_driver(runs)

    def test_preserves_and_rejects_a_failed_process_record(self) -> None:
        runs = [run("z3"), run("axeyum")]
        runs[0] = {
            "backend": "z3",
            "repetition": 1,
            "position": 1,
            "run_error": "canonical model policy did not complete every attempt",
        }
        with self.assertRaisesRegex(RuntimeError, "process failures: z3 repetition 1"):
            MODULE.summarize_driver(runs)

    def test_summarizes_stable_canonical_model_choice_populations(self) -> None:
        runs = [run("z3"), run("z3"), run("axeyum"), run("axeyum")]
        for candidate in runs:
            candidate["canonical_model_choice"] = {
                "policy": "glaurung-min-unsigned-v1",
                "attempts": 2 if candidate["backend"] == "z3" else 3,
                "completed": 2 if candidate["backend"] == "z3" else 3,
                "infeasible": 0,
                "probes": 130 if candidate["backend"] == "z3" else 195,
                "inconclusive": 0,
                "unsupported_width": 0,
                "unknown": 0,
                "no_solver": 0,
                "error": 0,
                "final_unsat": 0,
            }
        summary = MODULE.summarize_driver(runs)
        self.assertEqual(
            summary["canonical_model_choice"]["backends"]["z3"]["attempts"], 2
        )
        self.assertEqual(
            summary["canonical_model_choice"]["backends"]["axeyum"]["attempts"],
            3,
        )

    def test_rejects_canonical_model_choice_telemetry_drift(self) -> None:
        runs = [run("z3"), run("z3"), run("axeyum"), run("axeyum")]
        for candidate in runs:
            candidate["canonical_model_choice"] = {
                "policy": "glaurung-min-unsigned-v1",
                "attempts": 2,
                "completed": 2,
                "infeasible": 0,
                "probes": 130,
                "inconclusive": 0,
                "unsupported_width": 0,
                "unknown": 0,
                "no_solver": 0,
                "error": 0,
                "final_unsat": 0,
            }
        runs[1]["canonical_model_choice"]["probes"] = 129
        with self.assertRaisesRegex(RuntimeError, "canonical model telemetry drift"):
            MODULE.summarize_driver(runs)

    def test_accepts_stable_exact_authority_population(self) -> None:
        runs = [run("z3"), run("z3"), run("axeyum"), run("axeyum")]
        summary = MODULE.summarize_driver(runs)
        self.assertTrue(summary["exact_finding_parity"])
        self.assertEqual(
            summary["coverage"],
            {"analyzed": 10, "reachable": 100, "boundary": "fixed-work-limit"},
        )
        self.assertEqual(
            MODULE.finding_acceptance_failures(Path("driver"), summary), []
        )

    def test_rejects_stable_backend_divergence(self) -> None:
        runs = [run("z3"), run("z3"), run("axeyum"), run("axeyum")]
        for candidate in runs:
            if candidate["backend"] == "axeyum":
                candidate["findings"] = ["sink-b"]
                candidate["findings_sha256"] = "axeyum-hash"
        summary = MODULE.summarize_driver(runs)
        failures = MODULE.finding_acceptance_failures(Path("tcpip.sys"), summary)
        self.assertFalse(summary["exact_finding_parity"])
        self.assertEqual(len(failures), 1)
        self.assertIn("z3-only=1, axeyum-only=1", failures[0])

    def test_can_accept_high_confidence_parity_while_retaining_raw_divergence(
        self,
    ) -> None:
        runs = [run("z3"), run("z3"), run("axeyum"), run("axeyum")]
        for candidate in runs:
            candidate["high_confidence_findings"] = []
            candidate["high_confidence_finding_count"] = 0
            candidate["high_confidence_findings_sha256"] = MODULE.text_sha256([])
            candidate["reported_high_confidence"] = 0
            candidate["diagnostic_findings"] = candidate["findings"]
            candidate["diagnostic_finding_count"] = len(candidate["findings"])
            candidate["diagnostic_findings_sha256"] = candidate["findings_sha256"]
            candidate["reported_suppressed"] = len(candidate["findings"])
            if candidate["backend"] == "axeyum":
                candidate["findings"] = ["sink-b"]
                candidate["findings_sha256"] = "axeyum-hash"
                candidate["diagnostic_findings"] = ["sink-b"]
                candidate["diagnostic_findings_sha256"] = "axeyum-hash"
        summary = MODULE.summarize_driver(runs)
        self.assertFalse(summary["exact_raw_finding_parity"])
        self.assertTrue(summary["exact_high_confidence_finding_parity"])
        self.assertNotEqual(summary["raw"]["z3_only"], [])
        self.assertEqual(summary["high_confidence"]["z3_only"], [])
        self.assertEqual(
            MODULE.finding_acceptance_failures(
                Path("tcpip.sys"), summary, "high-confidence"
            ),
            [],
        )
        self.assertNotEqual(
            MODULE.finding_acceptance_failures(Path("tcpip.sys"), summary, "raw"),
            [],
        )

    def test_high_confidence_acceptance_fails_closed_without_partition(self) -> None:
        runs = [run("z3"), run("z3"), run("axeyum"), run("axeyum")]
        for candidate in runs:
            candidate["confidence_partition_available"] = False
            for key in (
                "reported_high_confidence",
                "high_confidence_finding_count",
                "high_confidence_findings_sha256",
                "high_confidence_findings",
                "diagnostic_finding_count",
                "diagnostic_findings_sha256",
                "diagnostic_findings",
            ):
                candidate.pop(key, None)
        summary = MODULE.summarize_driver(runs)
        self.assertIsNone(summary["exact_high_confidence_finding_parity"])
        failures = MODULE.finding_acceptance_failures(
            Path("legacy.sys"), summary, "high-confidence"
        )
        self.assertEqual(len(failures), 1)
        self.assertIn("finding partition unavailable", failures[0])

    def test_preserves_summary_for_unstable_backend_output(self) -> None:
        runs = [run("z3"), run("z3"), run("axeyum"), run("axeyum")]
        runs[1]["findings"] = ["sink-a", "unstable-z3-sink"]
        runs[1]["findings_sha256"] = "z3-drift"
        runs[1]["finding_count"] = 2
        summary = MODULE.summarize_driver(runs)
        failures = MODULE.finding_acceptance_failures(Path("tcpip.sys"), summary)
        self.assertFalse(summary["within_backend_stable"])
        self.assertEqual(summary["stability"]["z3"]["stable_finding_count"], 1)
        self.assertEqual(summary["stability"]["z3"]["union_finding_count"], 2)
        self.assertEqual(
            summary["stability"]["z3"]["unstable_findings"], ["unstable-z3-sink"]
        )
        self.assertTrue(
            any("z3 finding output unstable" in failure for failure in failures)
        )


if __name__ == "__main__":
    unittest.main()
