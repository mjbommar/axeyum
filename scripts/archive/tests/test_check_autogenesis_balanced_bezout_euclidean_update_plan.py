from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-balanced-bezout-euclidean-update-plan.py"
SPEC = importlib.util.spec_from_file_location("balanced_bezout_euclidean_update_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BalancedBezoutEuclideanUpdatePlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.BalancedBezoutEuclideanUpdatePlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_witness_map_drift(self) -> None:
        self.reject(lambda value: value["construction"]["witness_map"].__setitem__("new_nn", "np"))

    def test_rejects_ring_normalization(self) -> None:
        self.reject(lambda value: value["construction"].__setitem__("ring_normalization_used", True))

    def test_rejects_public_quotient(self) -> None:
        self.reject(lambda value: value["construction"].__setitem__("public_quotient_used", True))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1))

    def test_rejects_extra_compilation(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_source_compilations", 2))

    def test_rejects_generic_gcd_submission(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_generic_gcd_submissions", 1))

    def test_rejects_generic_theorem_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("generic_balanced_bezout_credit", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
