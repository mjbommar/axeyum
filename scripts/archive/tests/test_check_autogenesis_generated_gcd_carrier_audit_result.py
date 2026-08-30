from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-generated-gcd-carrier-audit-result.py"
SPEC = importlib.util.spec_from_file_location("generated_gcd_carrier_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class GeneratedGcdCarrierAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(
            MODULE.GeneratedGcdCarrierAuditResultError,
            "measured carrier result",
        ):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_dependency_change_is_rejected(self) -> None:
        self.reject(lambda value: value["carrier"]["direct_theorem_dependencies"].pop())

    def test_frontier_change_is_rejected(self) -> None:
        self.reject(lambda value: value["novel_dependency_frontier"].pop())

    def test_reconstruction_credit_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("reconstruction_source_compilations", 1)
        )

    def test_ledger_credit_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
