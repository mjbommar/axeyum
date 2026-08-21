from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-dvd-antisymm-dependency-audit-result.py"
SPEC = importlib.util.spec_from_file_location("dvd_antisymm_dependency_audit_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class DvdAntisymmDependencyAuditResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.DvdAntisymmDependencyAuditResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_root_reordering(self) -> None:
        self.reject(lambda value: value["rows"].reverse())

    def test_rejects_clean_carrier(self) -> None:
        self.reject(lambda value: value["rows"][3].__setitem__("axiom_footprint", []))

    def test_rejects_second_carrier(self) -> None:
        self.reject(lambda value: value["rows"][2].__setitem__("axiom_footprint", ["propext"]))

    def test_rejects_summary_change(self) -> None:
        self.reject(lambda value: value["summary"].__setitem__("empty_footprint", 5))

    def test_rejects_rendering_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("theorem_types_rendered", 1))

    def test_rejects_target_submission(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("exact_target_submissions", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
