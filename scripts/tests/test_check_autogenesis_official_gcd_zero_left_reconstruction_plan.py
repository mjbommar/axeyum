from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-zero-left-reconstruction-plan.py"
SPEC = importlib.util.spec_from_file_location("official_gcd_zero_left_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialGcdZeroLeftPlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialGcdZeroLeftPlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_target_drift(self) -> None:
        self.reject(lambda value: value["construction"].__setitem__("target", "Nat.gcd_zero_left"))

    def test_rejects_support_drift(self) -> None:
        self.reject(lambda value: value["construction"].__setitem__("new_support_theorem", "Nat.gcd_zero_left"))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1))

    def test_rejects_second_submission(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_new_theorem_submissions", 2))

    def test_rejects_closed_submission(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_closed_balanced_bezout_submissions", 1))

    def test_rejects_zero_left_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("official_gcd_zero_left_credit", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
