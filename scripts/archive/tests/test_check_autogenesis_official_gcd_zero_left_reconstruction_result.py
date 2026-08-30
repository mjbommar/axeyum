from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-zero-left-reconstruction-result.py"
SPEC = importlib.util.spec_from_file_location("official_gcd_zero_left_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialGcdZeroLeftResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialGcdZeroLeftResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_record_limit_drift(self) -> None:
        self.reject(lambda value: value["decline"].__setitem__("limit", 3000000))

    def test_rejects_root_selection_claim(self) -> None:
        self.reject(lambda value: value["decline"].__setitem__("root_selection_used", True))

    def test_rejects_successful_import(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("successful_importer_runs", 1))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("retries", 1))

    def test_rejects_limit_increase(self) -> None:
        self.reject(lambda value: value["next_boundary"].__setitem__("importer_limit_increase_authorized", True))

    def test_rejects_source_change(self) -> None:
        self.reject(lambda value: value["next_boundary"].__setitem__("source_proof_change_authorized", True))

    def test_rejects_theorem_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("official_gcd_zero_left_credit", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
