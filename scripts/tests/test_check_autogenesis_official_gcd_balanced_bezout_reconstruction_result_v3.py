from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-result-v3.py"
SPEC = importlib.util.spec_from_file_location("balanced_bezout_result_v3", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BalancedBezoutResultV3Tests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.BalancedBezoutResultV3Error):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_second_import(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("importer_runs", 2))

    def test_rejects_empty_helper_claim(self) -> None:
        self.reject(lambda value: value["roots"][0]["axiom_footprint"].clear())

    def test_rejects_missing_propext(self) -> None:
        self.reject(lambda value: value["roots"][1]["axiom_footprint"].pop())

    def test_rejects_tactic_route_acceptance(self) -> None:
        self.reject(lambda value: value["next_boundary"].__setitem__("lean_tactic_source_route_accepted", True))

    def test_rejects_compilation_credit(self) -> None:
        self.reject(lambda value: value["next_boundary"].__setitem__("reuse_compilation_as_theorem_credit", True))

    def test_rejects_baseline_drift(self) -> None:
        self.reject(lambda value: value["cleanup"].__setitem__("preexisting_baseline_unchanged", False))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
