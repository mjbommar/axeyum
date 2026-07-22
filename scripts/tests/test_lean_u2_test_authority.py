from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "gen_lean_u2_test_authority",
    ROOT / "scripts" / "gen-lean-u2-test-authority.py",
)
assert SPEC and SPEC.loader
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class LeanU2TestAuthorityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = GEN.read_manifest()

    def failures(self) -> list[str]:
        return GEN.validate_manifest(self.data)

    def test_committed_capture_is_valid_deterministic_and_non_terminal(self) -> None:
        self.assertEqual(self.failures(), [])
        first = GEN.summarize(self.data)
        second = GEN.summarize(GEN.read_manifest())
        self.assertEqual(first, second)
        self.assertEqual(first["verdict"], "registration bounded; complete U2 parity authority not established")
        self.assertEqual(first["outcomes"]["state"], "not-run")
        markdown = GEN.render_markdown(first)
        self.assertIn("3,678", markdown)
        self.assertIn("3,723", markdown)
        self.assertIn("No official execution, Axeyum execution", markdown)

    def test_profile_case_kind_and_output_denominators_are_exact(self) -> None:
        report = GEN.summarize(self.data)
        self.assertEqual(
            [(item["id"], item["registered"]) for item in report["profiles"]],
            [("default", 3678), ("full-lake", 3723)],
        )
        self.assertEqual(report["selection_relation"], {"default_only": 0, "full_lake_only": 45})
        self.assertEqual(
            report["kind_counts"],
            {"directory": 31, "lake-directory": 52, "lint": 1, "pile": 3639},
        )
        self.assertEqual(
            report["output_policy_counts"],
            {"empty": 2099, "exact": 1480, "ignored": 60, "script-defined": 84},
        )

    def test_complete_git_content_and_pile_accounting_close(self) -> None:
        report = GEN.summarize(self.data)
        self.assertEqual(
            [(item["path"], item["files"]) for item in report["content"]["roots"]],
            [("doc/examples", 73), ("tests", 6931)],
        )
        self.assertEqual(report["content"]["files"], 7004)
        accounting = report["selection_accounting"]
        self.assertEqual(accounting["glob_candidates"], 3660)
        self.assertEqual(accounting["registered"], 3639)
        self.assertEqual(accounting["excluded"], 21)
        self.assertEqual(
            accounting["excluded_by_reason"],
            {"no-test-runner": 11, "no-test-sidecar": 7, "runner-name": 3},
        )

    def test_profile_aggregate_mutation_is_rejected(self) -> None:
        self.data["capture"]["profiles"][0]["registered"] += 1
        self.assertTrue(any("capture profile default" in item for item in self.failures()))

    def test_primary_expected_output_and_case_digest_mutations_are_rejected(self) -> None:
        case = next(item for item in self.data["cases"] if item["output_policy"] == "exact")
        case["source_sha256"] = "0" * 64
        case["expected_path"] = None
        failures = self.failures()
        self.assertTrue(any("primary source digest drift" in item for item in failures))
        self.assertTrue(any("expected-output identity drift" in item for item in failures))
        self.assertTrue(any("case digest drift" in item for item in failures))

    def test_support_scope_and_content_aggregate_mutations_are_rejected(self) -> None:
        self.data["support_scopes"][0]["sha256"] = "0" * 64
        self.data["content_roots"][0]["files"] += 1
        failures = self.failures()
        self.assertTrue(any("support scope" in item and "aggregate drift" in item for item in failures))
        self.assertTrue(any("content root" in item and "aggregate drift" in item for item in failures))

    def test_execution_or_pairing_credit_is_rejected(self) -> None:
        self.data["outcomes"]["official_executed"] = 3723
        self.assertTrue(any("cannot claim execution" in item for item in self.failures()))

    def test_target_and_selection_relation_drift_are_rejected(self) -> None:
        self.data["target"]["commit"] = "0" * 40
        self.data["capture"]["full_lake_only"] = 44
        failures = self.failures()
        self.assertTrue(any("exact Lean v4.30.0 pin" in item for item in failures))
        self.assertTrue(any("full-lake-only count drift" in item for item in failures))


if __name__ == "__main__":
    unittest.main()
