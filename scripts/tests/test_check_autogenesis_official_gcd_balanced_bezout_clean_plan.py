from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-clean-plan.py"
SPEC = importlib.util.spec_from_file_location("official_gcd_balanced_bezout_clean_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialGcdBalancedBezoutCleanPlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialGcdBalancedBezoutCleanPlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_required_dependency_loss(self) -> None:
        self.reject(lambda value: value["construction"]["required_direct_dependencies"].pop())

    def test_rejects_gcd_specialization(self) -> None:
        self.reject(lambda value: value["construction"].__setitem__("gcd_leaf_specialization_in_this_increment", True))

    def test_rejects_extra_compilation(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_source_compilations", 7))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1))

    def test_rejects_target_submission(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_exact_fibonacci_target_submissions", 1))

    def test_rejects_target_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("target_specialization_credit", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
