from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-subtractive-gcd-root-audit-result.py"
SPEC = importlib.util.spec_from_file_location("subtractive_gcd_root_audit_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SubtractiveGcdRootAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.SubtractiveGcdAuditResultError, message):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_empty_root_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["rows"][0].__setitem__("accepted", True),
            "measured subtractive gcd audit",
        )

    def test_dependency_removal_is_rejected(self) -> None:
        self.reject(
            lambda value: value["direct_dependency_union"].pop(),
            "measured subtractive gcd audit",
        )

    def test_bezout_compilation_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("bezout_source_compilations", 1),
            "measured subtractive gcd audit",
        )

    def test_ledger_credit_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("ledger_writes", 1),
            "measured subtractive gcd audit",
        )


if __name__ == "__main__":
    unittest.main()
