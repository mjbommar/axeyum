from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-int-fib-neg-dependency-audit-result.py"
SPEC = importlib.util.spec_from_file_location("int_fib_neg_dependency_audit_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class IntFibNegDependencyAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.IntFibNegDependencyAuditResultError, message):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_clean_root_omission_is_rejected(self) -> None:
        self.reject(lambda value: value["empty_footprint_roots"].pop(), "measured dependency result")

    def test_bearing_root_omission_is_rejected(self) -> None:
        self.reject(lambda value: value["assumption_bearing_roots"].pop(), "measured dependency result")

    def test_direct_composition_authority_is_rejected(self) -> None:
        self.reject(lambda value: value["decision"].__setitem__("direct_official_composition_authorized", True), "measured dependency result")

    def test_ledger_write_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1), "measured dependency result")


if __name__ == "__main__":
    unittest.main()
