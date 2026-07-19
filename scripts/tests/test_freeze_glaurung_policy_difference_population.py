from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "freeze-glaurung-policy-difference-population.py"
SPEC = importlib.util.spec_from_file_location("freeze_policy_differences", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def finding(kind: str, va: str, taint: str) -> str:
    return f"    {kind}  va={va}  [dispatch] fn=f @ 0x1000  sev=Constrained  taint=[\"{taint}\"]"


def report(rows: set[str]) -> dict:
    runs = []
    for repetition in (1, 2):
        for backend in ("z3", "axeyum"):
            runs.append(
                {
                    "backend": backend,
                    "repetition": repetition,
                    "findings": sorted(rows),
                }
            )
    return {
        "accepted": True,
        "all_drivers_exact_finding_parity": True,
        "drivers": [
            {
                "driver": {"path": "/fixtures/example.sys"},
                "runs": runs,
            }
        ],
    }


class FreezePolicyDifferencesTests(unittest.TestCase):
    def setUp(self) -> None:
        self.common = finding("arbitrary-read", "0x1010", "*SystemBuffer")
        self.varying = finding("null-deref", "0x1020", "Arg1")
        self.reports = {
            policy: report(
                {self.common, self.varying} if policy == "any-model" else {self.common}
            )
            for policy in MODULE.EXPECTED_POLICIES
        }
        self.source_manifest = {
            "drivers": [
                {
                    "name": "example.sys",
                    "binary_path": "fixtures/example.sys",
                    "sha256": "binary",
                    "source": {"path": "fixtures/example.c", "sha256": "source"},
                }
            ]
        }

    def test_freezes_exact_union_minus_intersection_as_pending(self) -> None:
        result = MODULE.freeze_population(
            reports=self.reports,
            report_hashes={policy: policy for policy in MODULE.EXPECTED_POLICIES},
            source_manifest=self.source_manifest,
            source_manifest_sha256="manifest",
            analysis_sha256="analysis",
        )
        self.assertEqual(result["finding_count"], 1)
        self.assertEqual(result["site_count"], 1)
        self.assertEqual(result["driver_count"], 1)
        row = result["drivers"][0]["rows"][0]
        self.assertEqual(row["finding"], self.varying)
        self.assertEqual(row["present_policies"], ["any-model"])
        self.assertEqual(row["adjudication"]["status"], "pending")
        self.assertIsNone(row["adjudication"]["classification"])

    def test_rejects_unstable_raw_population(self) -> None:
        self.reports["any-model"]["drivers"][0]["runs"][0]["findings"] = [self.common]
        with self.assertRaisesRegex(ValueError, "raw rows are unstable"):
            MODULE.freeze_population(
                reports=self.reports,
                report_hashes={policy: policy for policy in MODULE.EXPECTED_POLICIES},
                source_manifest=self.source_manifest,
                source_manifest_sha256="manifest",
                analysis_sha256="analysis",
            )

    def test_rejects_policy_order_drift(self) -> None:
        reports = dict(reversed(self.reports.items()))
        with self.assertRaisesRegex(ValueError, "policy order differs"):
            MODULE.freeze_population(
                reports=reports,
                report_hashes={},
                source_manifest=self.source_manifest,
                source_manifest_sha256="manifest",
                analysis_sha256="analysis",
            )


if __name__ == "__main__":
    unittest.main()
