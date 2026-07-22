"""Focused tests for the resumable distributed-run contract prototype."""

from __future__ import annotations

import importlib.util
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "gen-smtcomp-resume-contract.py"
SPEC = importlib.util.spec_from_file_location("gen_smtcomp_resume_contract", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class ResumeContractTests(unittest.TestCase):
    def source(self) -> dict:
        return json.loads(MODULE.SOURCE.read_text(encoding="utf-8"))

    def test_full_contract_passes(self) -> None:
        report = MODULE.evaluate(self.source())
        self.assertEqual(report["invariant_count"], 18)
        self.assertEqual(report["scenario_count"], 28)
        self.assertEqual(report["accepted_scenarios"], 5)
        self.assertEqual(report["rejected_scenarios"], 23)
        self.assertTrue(report["deterministic_resume_byte_equal"])
        self.assertTrue(report["timeout_response_retained"])

    def test_all_invariants_have_failure_or_control_coverage(self) -> None:
        report = MODULE.evaluate(self.source())
        declared = {row["id"] for row in report["invariants"]}
        covered = {item for row in report["scenarios"] for item in row["invariants"]}
        self.assertEqual(declared, covered)

    def test_unknown_invariant_is_rejected(self) -> None:
        source = self.source()
        source["scenarios"][0]["invariants"].append("R999")
        with self.assertRaisesRegex(MODULE.ContractError, "unknown invariant"):
            MODULE.evaluate(source)

    def test_missing_implemented_scenario_is_rejected(self) -> None:
        source = self.source()
        source["scenarios"].pop()
        with self.assertRaisesRegex(MODULE.ContractError, "scenario sets differ"):
            MODULE.evaluate(source)

    def test_expected_outcome_mutation_is_rejected(self) -> None:
        source = self.source()
        source["scenarios"][0]["expected"] = "reject"
        with self.assertRaisesRegex(MODULE.ContractError, "expected reject"):
            MODULE.evaluate(source)

    def test_declared_field_schema_drift_is_rejected(self) -> None:
        source = self.source()
        source["attempt_terminal_fields"].remove("peak_rss_bytes")
        with self.assertRaisesRegex(MODULE.ContractError, "executable contract"):
            MODULE.evaluate(source)


if __name__ == "__main__":
    unittest.main()
