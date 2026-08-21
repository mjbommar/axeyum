from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-extended-gcd-root-audit-result.py"
SPEC = importlib.util.spec_from_file_location("extended_gcd_root_audit_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ExtendedGcdRootAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(
            MODULE.ExtendedGcdRootAuditResultError,
            "measured extended-gcd result",
        ):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_empty_footprint_claim_is_rejected(self) -> None:
        self.reject(lambda value: value["row"]["axiom_footprint"].clear())

    def test_dependency_removal_is_rejected(self) -> None:
        self.reject(lambda value: value["row"]["direct_theorem_dependencies"].pop())

    def test_adapter_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["summary"].__setitem__(
                "coefficient_adapter_authorized", True
            )
        )

    def test_second_import_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("batch_importer_runs", 2)
        )

    def test_ledger_credit_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
