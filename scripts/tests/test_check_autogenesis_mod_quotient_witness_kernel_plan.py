from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-mod-quotient-witness-kernel-plan.py"
SPEC = importlib.util.spec_from_file_location("mod_quotient_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ModQuotientWitnessPlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.ModQuotientWitnessPlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_funext(self) -> None:
        self.reject(lambda value: value["construction"]["forbidden_dependencies"].remove("funext"))

    def test_rejects_binder_rewrite(self) -> None:
        self.reject(lambda value: value["construction"].__setitem__("rewrite_under_binder_used", True))

    def test_rejects_ring(self) -> None:
        self.reject(lambda value: value["construction"].__setitem__("ring_normalization_used", True))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1))

    def test_rejects_one_import(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_importer_runs", 1))

    def test_rejects_bezout_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("balanced_bezout_credit", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
