from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-balanced-bezout-euclidean-update-plan-v2.py"
SPEC = importlib.util.spec_from_file_location("balanced_bezout_euclidean_update_plan_v2", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BalancedBezoutEuclideanUpdatePlanV2Tests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.BalancedBezoutEuclideanUpdatePlanV2Error):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_leaf_loss(self) -> None:
        self.reject(lambda value: value["construction"]["replaced_dependencies"].pop())

    def test_rejects_contract_drift(self) -> None:
        self.reject(lambda value: value["construction"]["injected_leaf_contracts"].pop())

    def test_rejects_witness_map_drift(self) -> None:
        self.reject(lambda value: value["construction"]["witness_map"].__setitem__("new_nn", "np"))

    def test_rejects_leaf_composition(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_leaf_compositions", 1))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1))

    def test_rejects_generic_gcd(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_generic_gcd_submissions", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
