from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-balanced-bezout-euclidean-update-dependency-audit-result.py"
SPEC = importlib.util.spec_from_file_location("balanced_bezout_dependency_audit_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BalancedBezoutDependencyAuditResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.BalancedBezoutDependencyAuditResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_missing_carrier(self) -> None:
        self.reject(lambda value: value["summary"]["propext_carriers"].pop())

    def test_rejects_clean_root_loss(self) -> None:
        self.reject(lambda value: value["summary"]["clean_roots"].pop())

    def test_rejects_population_drift(self) -> None:
        self.reject(lambda value: value["summary"].__setitem__("population", 8))

    def test_rejects_rendering(self) -> None:
        self.reject(lambda value: value["summary"]["rendered_material"].__setitem__("proof_terms", 1))

    def test_rejects_broad_v2_rewrite(self) -> None:
        self.reject(lambda value: value["next_boundary"].__setitem__("unchanged_update_source_except_leaf_injection", False))

    def test_rejects_theorem_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("euclidean_update_credit", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
