"""Mutation controls for the cancellation-to-Acc audit and next plan."""

from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]


def module(name: str, path: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    assert spec and spec.loader
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


AUDIT = module("acc_path_result", "scripts/check-autogenesis-official-cancellation-acc-path-audit-result.py")
PLAN = module("acc_package_plan", "scripts/check-autogenesis-official-cancellation-acc-package-composition-plan.py")
COMPOSED = module("acc_package_result", "scripts/check-autogenesis-official-cancellation-acc-package-composition-result.py")


class AuditResultControls(unittest.TestCase):
    def test_live_sealed_result_passes(self) -> None:
        self.assertEqual(AUDIT.validate()["summary"]["nearest_carrier"], "Acc")

    def test_authority_mutation_fails(self) -> None:
        result = AUDIT.load(AUDIT.RESULT)
        result["authority"]["support_credit"] = 1
        with self.assertRaises(AUDIT.AuditResultError):
            AUDIT.validate(result)

    def test_nearest_package_mutation_fails(self) -> None:
        result = AUDIT.load(AUDIT.RESULT)
        result["summary"]["nearest_complete_package"][0] = "FakeAcc"
        with self.assertRaises(AUDIT.AuditResultError):
            AUDIT.validate(result)


class PackagePlanControls(unittest.TestCase):
    def test_live_plan_passes(self) -> None:
        self.assertEqual(PLAN.validate()["execution"]["exact_target_submissions"], 0)

    def test_identity_mutation_fails(self) -> None:
        plan = copy.deepcopy(PLAN.load(PLAN.PLAN))
        plan["authorized_recursive_package"]["exact_source_declaration_sha256"]["Acc"] = "0" * 64
        with self.assertRaises(PLAN.CompositionPlanError):
            PLAN.validate(plan)


class PackageCompositionResultControls(unittest.TestCase):
    def test_live_composition_result_passes(self) -> None:
        self.assertEqual(COMPOSED.validate()["authority"]["cancellation_composition_credit"], 1)

    def test_downstream_authority_mutation_fails(self) -> None:
        result = copy.deepcopy(COMPOSED.load(COMPOSED.RESULT))
        result["authority"]["target_credit"] = 1
        with self.assertRaises(COMPOSED.CompositionResultError):
            COMPOSED.validate(result)

    def test_budget_mutation_fails(self) -> None:
        plan = copy.deepcopy(PLAN.load(PLAN.PLAN))
        plan["execution"]["retries"] = 1
        with self.assertRaises(PLAN.CompositionPlanError):
            PLAN.validate(plan)


if __name__ == "__main__":
    unittest.main()
