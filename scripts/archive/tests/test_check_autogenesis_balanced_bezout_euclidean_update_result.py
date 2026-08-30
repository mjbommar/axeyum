from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-balanced-bezout-euclidean-update-result.py"
SPEC = importlib.util.spec_from_file_location("balanced_bezout_euclidean_update_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BalancedBezoutEuclideanUpdateResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.BalancedBezoutEuclideanUpdateResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_second_import(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("importer_runs", 2))

    def test_rejects_empty_footprint_claim(self) -> None:
        self.reject(lambda value: value["theorem"]["axiom_footprint"].clear())

    def test_rejects_dependency_drift(self) -> None:
        self.reject(lambda value: value["theorem"]["direct_theorem_dependencies"].pop())

    def test_rejects_theorem_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("euclidean_update_credit", 1))

    def test_rejects_reuse_as_credit(self) -> None:
        self.reject(lambda value: value["next_boundary"].__setitem__("reuse_compilation_as_theorem_credit", True))

    def test_rejects_baseline_drift(self) -> None:
        self.reject(lambda value: value["cleanup"].__setitem__("preexisting_baseline_unchanged", False))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
