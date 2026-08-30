from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-clean-result.py"
SPEC = importlib.util.spec_from_file_location("official_gcd_balanced_bezout_clean_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialGcdBalancedBezoutCleanResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialGcdBalancedBezoutCleanResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_dependency_loss(self) -> None:
        self.reject(lambda value: value["theorem"]["direct_theorem_dependencies"].pop())

    def test_rejects_axiom_footprint(self) -> None:
        self.reject(lambda value: value["theorem"]["axiom_footprint"].append("propext"))

    def test_rejects_one_reconstruction(self) -> None:
        self.reject(lambda value: value["theorem"].__setitem__("fresh_reconstructions", 1))

    def test_rejects_generic_credit_loss(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("generic_balanced_bezout_credit", 0))

    def test_rejects_gcd_leaf_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("gcd_leaf_specialization_credit", 1))

    def test_rejects_cancellation_authorization(self) -> None:
        self.reject(lambda value: value["next_boundary"].__setitem__("cancellation_authorized", True))

    def test_rejects_cleanup_drift(self) -> None:
        self.reject(lambda value: value["cleanup"].__setitem__("exact_temporary_paths_removed", 17))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
