from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-generic-base-plan.py"
SPEC = importlib.util.spec_from_file_location("official_gcd_balanced_bezout_generic_base_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialGcdBalancedBezoutGenericBasePlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialGcdBalancedBezoutGenericBasePlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_predecessor_change(self) -> None:
        self.reject(lambda value: value["predecessor"].__setitem__("sha256", "0" * 64))

    def test_rejects_base_change(self) -> None:
        self.reject(lambda value: value["acceptance"].__setitem__("composition_base", "r082"))

    def test_rejects_generic_composition(self) -> None:
        self.reject(lambda value: value["acceptance"].__setitem__("generic_composition_operations", 1))

    def test_rejects_root_loss(self) -> None:
        self.reject(lambda value: value["acceptance"]["composed_roots"].pop())

    def test_rejects_proof_rendering(self) -> None:
        self.reject(lambda value: value["implementation"].__setitem__("proof_terms_types_or_values_may_be_rendered", True))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1))

    def test_rejects_closed_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("closed_gcd_balanced_bezout_credit", 1))

    def test_rejects_target_submission(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_exact_fibonacci_target_submissions", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
