from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-balanced-bezout-clean-mul-leaves-result.py"
SPEC = importlib.util.spec_from_file_location("balanced_bezout_clean_mul_leaves_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BalancedBezoutCleanMulLeavesResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.BalancedBezoutCleanMulLeavesResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_leaf_loss(self) -> None:
        self.reject(lambda value: value["theorems"].pop())

    def test_rejects_axiom_footprint(self) -> None:
        self.reject(lambda value: value["theorems"][0]["axiom_footprint"].append("propext"))

    def test_rejects_nonidentical_audits(self) -> None:
        self.reject(lambda value: value["audit"].__setitem__("audits_byte_identical", False))

    def test_rejects_leaf_credit_loss(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("clean_leaf_credit", 1))

    def test_rejects_update_composition(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("euclidean_update_composition_credit", 1))

    def test_rejects_generic_gcd_authorization(self) -> None:
        self.reject(lambda value: value["next_boundary"].__setitem__("generic_gcd_submission_authorized", True))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
