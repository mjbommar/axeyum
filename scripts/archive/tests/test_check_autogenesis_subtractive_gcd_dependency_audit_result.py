from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-subtractive-gcd-dependency-audit-result.py"
SPEC = importlib.util.spec_from_file_location("subtractive_gcd_dependency_audit_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SubtractiveGcdDependencyAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(
            MODULE.SubtractiveGcdDependencyAuditResultError,
            "measured dependency audit",
        ):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_class_change_is_rejected(self) -> None:
        self.reject(lambda value: value["rows"][2].__setitem__("class", "empty-footprint"))

    def test_route_carrier_removal_is_rejected(self) -> None:
        self.reject(lambda value: value["route_relevant_assumption_carriers"].pop())

    def test_frontier_removal_is_rejected(self) -> None:
        self.reject(lambda value: value["route_relevant_novel_dependency_frontier"].pop())

    def test_replacement_credit_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("replacement_source_compilations", 1)
        )

    def test_ledger_credit_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
