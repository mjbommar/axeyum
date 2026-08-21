from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-balanced-bezout-euclidean-update-dependency-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("balanced_bezout_dependency_audit_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BalancedBezoutDependencyAuditPlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.BalancedBezoutDependencyAuditPlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_root_loss(self) -> None:
        self.reject(lambda value: value["ordered_roots"].pop())

    def test_rejects_root_reorder(self) -> None:
        self.reject(lambda value: value["ordered_roots"].reverse())

    def test_rejects_second_import(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_importer_runs", 2))

    def test_rejects_compilation(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_compiler_invocations", 1))

    def test_rejects_rendering(self) -> None:
        self.reject(lambda value: value["tool"].__setitem__("renders_proof_terms_types_or_values", True))

    def test_rejects_theorem_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("euclidean_update_credit", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
