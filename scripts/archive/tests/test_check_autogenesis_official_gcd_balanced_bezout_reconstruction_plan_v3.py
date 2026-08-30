from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-plan-v3.py"
SPEC = importlib.util.spec_from_file_location("balanced_bezout_plan_v3", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BalancedBezoutPlanV3Tests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.BalancedBezoutPlanV3Error):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_missing_correction(self) -> None:
        self.reject(lambda value: value["corrections"].pop())

    def test_rejects_source_drift(self) -> None:
        self.reject(lambda value: value["inputs"]["corrected_source"].__setitem__("sha256", "0" * 64))

    def test_rejects_public_quotient(self) -> None:
        self.reject(lambda value: value["construction"].__setitem__("public_quotient_used", True))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1))

    def test_rejects_import_shortfall(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_importer_runs", 1))

    def test_rejects_specialization(self) -> None:
        self.reject(lambda value: value["acceptance"].__setitem__("specialization_authorized_in_this_increment", True))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
