from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-int-fib-neg-natcast-dependency-audit-result.py"
SPEC = importlib.util.spec_from_file_location("int_fib_neg_natcast_dependency_audit_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class IntFibNegNatcastDependencyAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaises(MODULE.IntFibNegNatcastDependencyAuditResultError):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_clean_population_is_bound(self) -> None:
        self.reject(lambda value: value["empty_footprint_roots"].pop())

    def test_successor_is_fail_closed(self) -> None:
        self.reject(lambda value: value["decision"].__setitem__("official_natcast_composition_authorized", True))

    def test_ledger_authority_is_zero(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
