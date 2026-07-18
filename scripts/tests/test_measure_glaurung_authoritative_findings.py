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


def run(backend: str, *, analyzed: int = 10, boundary: str = "fixed-work-limit") -> dict:
    findings = ["sink-a"]
    return {
        "backend": backend,
        "finding_count": 1,
        "findings_sha256": "hash",
        "findings": findings,
        "reported_raw": 1,
        "reported_lines": 1,
        "reported_suppressed": 0,
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
        with self.assertRaisesRegex(RuntimeError, "authority coverage populations differ"):
            MODULE.summarize_driver(runs)

    def test_accepts_stable_exact_authority_population(self) -> None:
        runs = [run("z3"), run("z3"), run("axeyum"), run("axeyum")]
        summary = MODULE.summarize_driver(runs)
        self.assertTrue(summary["exact_finding_parity"])
        self.assertEqual(
            summary["coverage"],
            {"analyzed": 10, "reachable": 100, "boundary": "fixed-work-limit"},
        )
        self.assertEqual(MODULE.finding_acceptance_failures(Path("driver"), summary), [])

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


if __name__ == "__main__":
    unittest.main()
