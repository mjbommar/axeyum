import importlib.util
import hashlib
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "validate-glaurung-finding-population.py"
SPEC = importlib.util.spec_from_file_location(
    "validate_glaurung_finding_population", SCRIPT
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def manifest(expected: list[str] | None = None) -> dict:
    expected = ["validated-a", "validated-b"] if expected is None else expected
    return {
        "schema": "axeyum.glaurung-validated-finding-manifest.v1",
        "name": "source-backed-positive-control",
        "validation_policy": "exact-high-confidence-set",
        "source_repository": {
            "revision": "source-rev",
            "tracked_fixture_tree_clean": True,
        },
        "drivers": [
            {
                "name": "fixture.sys",
                "binary_path": "test_drivers/fixture.sys",
                "sha256": "driver-sha",
                "source": {
                    "repository_revision": "source-rev",
                    "path": "test_drivers/fixture.c",
                    "sha256": "source-sha",
                },
                "validation_basis": [
                    {
                        "finding": "validated-a",
                        "source_lines": "20-21",
                        "machine_evidence": "direct dangerous instruction",
                    },
                    {
                        "finding": "validated-b",
                        "source_lines": "30-31",
                        "machine_evidence": "direct dangerous call",
                    },
                ],
                "expected_findings": expected,
            }
        ],
    }


def authority_report(
    z3: list[str] | None = None,
    axeyum: list[str] | None = None,
    *,
    schema: str = "v5",
) -> dict:
    z3 = ["validated-a", "validated-b"] if z3 is None else z3
    axeyum = z3 if axeyum is None else axeyum
    runs = []
    for repetition in (1, 2):
        for backend, findings in (("z3", z3), ("axeyum", axeyum)):
            run = {
                "backend": backend,
                "repetition": repetition,
                "confidence_partition_available": True,
                "high_confidence_findings": findings,
                "high_confidence_finding_count": len(findings),
                "diagnostic_findings": ["diagnostic"],
                "finding_count": len(findings) + 1,
            }
            if schema == "v6":
                run["exploration_limits"] = {
                    "runs": 2,
                    "completed": 1,
                    "state_budget": 1,
                    "solve_budget": 0,
                    "timeout_budget": 0,
                    "deadline": 0,
                }
            runs.append(run)
    exact = z3 == axeyum
    return {
        "schema": f"axeyum.glaurung-authoritative-finding-parity.{schema}",
        "accepted": exact,
        "acceptance_population": "high-confidence",
        "all_drivers_exact_high_confidence_finding_parity": exact,
        "deterministic_worklists_required": schema == "v6",
        "glaurung": {"revision": "glaurung-rev", "tracked_dirty": False},
        "axeyum": {"revision": "axeyum-rev", "tracked_dirty": False},
        "post_run_source_identity": {
            "stable": True,
            "glaurung": {
                "revision": "glaurung-rev",
                "tracked_dirty": False,
            },
            "axeyum": {
                "revision": "axeyum-rev",
                "tracked_dirty": False,
            },
        },
        "drivers": [
            {
                "driver": {"path": "/fixtures/fixture.sys", "sha256": "driver-sha"},
                "runs": runs,
                "summary_error": None,
                "summary": {
                    "confidence_partition_available": True,
                    "exact_high_confidence_finding_parity": exact,
                    "high_confidence": {
                        "exact_finding_parity": exact,
                        "stability": {
                            "z3": {"output_stable": True},
                            "axeyum": {"output_stable": True},
                        },
                    },
                    "deterministic_worklists_verified": schema == "v6",
                    "exploration_limits": (
                        {
                            "backends": {
                                backend: {
                                    "runs": 2,
                                    "completed": 1,
                                    "state_budget": 1,
                                    "solve_budget": 0,
                                    "timeout_budget": 0,
                                    "deadline": 0,
                                }
                                for backend in ("z3", "axeyum")
                            }
                        }
                        if schema == "v6"
                        else None
                    ),
                },
            }
        ],
    }


class ValidatedFindingPopulationTests(unittest.TestCase):
    def test_accepts_exact_nonzero_source_validated_population(self) -> None:
        result = MODULE.validate_population(manifest(), authority_report())
        self.assertTrue(result["accepted"])
        self.assertEqual(result["validated_finding_count"], 2)
        self.assertEqual(result["observed_high_confidence_count"], 2)
        self.assertEqual(result["true_positive_count"], 2)
        self.assertEqual(result["false_negative_count"], 0)
        self.assertEqual(result["unexpected_high_confidence_count"], 0)
        self.assertEqual(result["recall"], 1.0)
        self.assertEqual(result["precision"], 1.0)

    def test_accepts_v6_only_with_rechecked_deterministic_worklists(self) -> None:
        result = MODULE.validate_population(
            manifest(), authority_report(schema="v6")
        )
        self.assertTrue(result["accepted"])

        missing = authority_report(schema="v6")
        missing["drivers"][0]["runs"][0].pop("exploration_limits")
        rejected_missing = MODULE.validate_population(manifest(), missing)
        self.assertFalse(rejected_missing["accepted"])
        self.assertTrue(
            any(
                "lacks exploration-limit telemetry" in row
                for row in rejected_missing["failures"]
            )
        )

        deadline = authority_report(schema="v6")
        limits = deadline["drivers"][0]["runs"][0]["exploration_limits"]
        limits["completed"] = 0
        limits["deadline"] = 1
        rejected_deadline = MODULE.validate_population(manifest(), deadline)
        self.assertFalse(rejected_deadline["accepted"])
        self.assertTrue(
            any(
                "deadline/timeout stop" in row
                for row in rejected_deadline["failures"]
            )
        )

    def test_retains_false_negative_and_rejects_incomplete_recall(self) -> None:
        result = MODULE.validate_population(
            manifest(), authority_report(["validated-a"])
        )
        self.assertFalse(result["accepted"])
        self.assertEqual(result["false_negative_count"], 1)
        self.assertEqual(result["drivers"][0]["false_negatives"], ["validated-b"])
        self.assertIn("validated findings were missed", result["failures"][0])

    def test_retains_unexpected_high_row_and_rejects_precision_drift(self) -> None:
        observed = ["validated-a", "validated-b", "producer-only"]
        result = MODULE.validate_population(manifest(), authority_report(observed))
        self.assertFalse(result["accepted"])
        self.assertEqual(result["unexpected_high_confidence_count"], 1)
        self.assertEqual(
            result["drivers"][0]["unexpected_high_confidence"], ["producer-only"]
        )
        self.assertTrue(any("unexpected high-confidence" in row for row in result["failures"]))

    def test_rejects_authority_divergence_or_unstable_source_identity(self) -> None:
        divergent = MODULE.validate_population(
            manifest(), authority_report(["validated-a"], ["validated-b"])
        )
        self.assertFalse(divergent["accepted"])
        self.assertTrue(any("authority report was not accepted" in row for row in divergent["failures"]))

        unstable_report = authority_report()
        unstable_report["post_run_source_identity"]["stable"] = False
        unstable = MODULE.validate_population(manifest(), unstable_report)
        self.assertFalse(unstable["accepted"])
        self.assertTrue(any("source identity changed" in row for row in unstable["failures"]))

    def test_rejects_driver_identity_drift_and_empty_denominator(self) -> None:
        wrong_driver = authority_report()
        wrong_driver["drivers"][0]["driver"]["sha256"] = "other"
        drift = MODULE.validate_population(manifest(), wrong_driver)
        self.assertFalse(drift["accepted"])
        self.assertTrue(any("driver population differs" in row for row in drift["failures"]))

        empty = MODULE.validate_population(manifest([]), authority_report([], []))
        self.assertFalse(empty["accepted"])
        self.assertTrue(any("validated denominator is empty" in row for row in empty["failures"]))

    def test_rechecks_basis_coverage_and_per_run_stability(self) -> None:
        bad_manifest = manifest()
        bad_manifest["drivers"][0]["validation_basis"].pop()
        bad_basis = MODULE.validate_population(bad_manifest, authority_report())
        self.assertFalse(bad_basis["accepted"])
        self.assertTrue(
            any("validation basis does not exactly cover" in row for row in bad_basis["failures"])
        )

        unstable_report = authority_report()
        unstable_report["drivers"][0]["runs"][-1]["high_confidence_findings"] = [
            "validated-a"
        ]
        unstable_report["drivers"][0]["runs"][-1]["high_confidence_finding_count"] = 1
        unstable = MODULE.validate_population(manifest(), unstable_report)
        self.assertFalse(unstable["accepted"])
        self.assertTrue(
            any("vary across repetitions" in row for row in unstable["failures"])
        )

        single_repetition = authority_report()
        single_repetition["drivers"][0]["runs"] = [
            row
            for row in single_repetition["drivers"][0]["runs"]
            if row["repetition"] == 1
        ]
        too_narrow = MODULE.validate_population(manifest(), single_repetition)
        self.assertFalse(too_narrow["accepted"])
        self.assertTrue(
            any("at least two repetitions" in row for row in too_narrow["failures"])
        )

    def test_source_repository_verification_accepts_exact_files_and_rejects_drift(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            repository = Path(temp)
            source_path = repository / "test_drivers/fixture.c"
            binary_path = repository / "test_drivers/fixture.sys"
            source_path.parent.mkdir()
            source_path.write_bytes(b"source\n")
            binary_path.write_bytes(b"binary\n")
            subprocess.run(["git", "init", "-q"], cwd=repository, check=True)
            subprocess.run(
                ["git", "add", "test_drivers/fixture.c", "test_drivers/fixture.sys"],
                cwd=repository,
                check=True,
            )
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=Axeyum Test",
                    "-c",
                    "user.email=axeyum@example.invalid",
                    "commit",
                    "-qm",
                    "fixture",
                ],
                cwd=repository,
                check=True,
            )
            revision = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=repository,
                check=True,
                capture_output=True,
                text=True,
            ).stdout.strip()
            candidate = manifest()
            candidate["source_repository"]["revision"] = revision
            candidate["drivers"][0]["sha256"] = hashlib.sha256(b"binary\n").hexdigest()
            candidate["drivers"][0]["source"]["repository_revision"] = revision
            candidate["drivers"][0]["source"]["sha256"] = hashlib.sha256(b"source\n").hexdigest()

            exact = MODULE.verify_source_repository(candidate, repository)
            self.assertTrue(exact["accepted"])
            self.assertEqual(exact["verified_file_count"], 2)

            escaping = manifest()
            escaping["source_repository"]["revision"] = revision
            escaping["drivers"][0]["binary_path"] = "../outside.sys"
            unsafe = MODULE.verify_source_repository(escaping, repository)
            self.assertFalse(unsafe["accepted"])
            self.assertTrue(
                any("unsafe source fixture path" in row for row in unsafe["failures"])
            )

            source_path.write_bytes(b"changed\n")
            drift = MODULE.verify_source_repository(candidate, repository)
            self.assertFalse(drift["accepted"])
            self.assertTrue(any("tracked fixture tree is dirty" in row for row in drift["failures"]))
            self.assertTrue(any("SHA-256 mismatch" in row for row in drift["failures"]))


if __name__ == "__main__":
    unittest.main()
