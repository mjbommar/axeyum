from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-int-fib-neg-root-audit-result.py"
SPEC = importlib.util.spec_from_file_location("int_fib_neg_root_audit_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class IntFibNegRootAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.IntFibNegRootAuditResultError, message):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_footprint_omission_is_rejected(self) -> None:
        self.reject(lambda value: value["row"]["axiom_footprint"].pop(), "measured Int.fib_neg result")

    def test_dependency_omission_is_rejected(self) -> None:
        self.reject(lambda value: value["row"]["direct_theorem_dependencies"].pop(), "measured Int.fib_neg result")

    def test_capsule_authority_is_rejected(self) -> None:
        self.reject(lambda value: value["summary"].__setitem__("exact_capsule_composition_authorized", True), "measured Int.fib_neg result")

    def test_ledger_write_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1), "measured Int.fib_neg result")


if __name__ == "__main__":
    unittest.main()
