from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-subtractive-gcd-route-frontier-audit-result.py"
SPEC = importlib.util.spec_from_file_location("subtractive_gcd_route_frontier_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SubtractiveGcdRouteFrontierAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(
            MODULE.SubtractiveGcdRouteFrontierAuditResultError,
            "measured route audit",
        ):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_private_footprint_change_is_rejected(self) -> None:
        self.reject(lambda value: value["rows"][-1]["axiom_footprint"].clear())

    def test_generated_carrier_change_is_rejected(self) -> None:
        self.reject(lambda value: value["generated_gcd_carrier"].__setitem__("name", "other"))

    def test_replacement_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("replacement_source_compilations", 1)
        )

    def test_ledger_credit_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
