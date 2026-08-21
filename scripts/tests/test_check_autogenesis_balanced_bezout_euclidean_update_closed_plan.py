from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-balanced-bezout-euclidean-update-closed-plan.py"
SPEC = importlib.util.spec_from_file_location("balanced_bezout_closed_update_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BalancedBezoutClosedUpdatePlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.BalancedBezoutClosedUpdatePlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_dependency_loss(self) -> None:
        self.reject(lambda value: value["construction"]["exact_required_direct_dependencies"].pop())

    def test_rejects_new_proof_step(self) -> None:
        self.reject(lambda value: value["construction"].__setitem__("new_mathematical_proof_steps", 1))

    def test_rejects_extra_compilation(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_source_compilations", 4))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1))

    def test_rejects_generic_gcd(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_generic_gcd_submissions", 1))

    def test_rejects_target_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("target_specialization_credit", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
