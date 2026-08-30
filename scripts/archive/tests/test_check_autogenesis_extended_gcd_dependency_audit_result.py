from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-extended-gcd-dependency-audit-result.py"
SPEC = importlib.util.spec_from_file_location("extended_gcd_dependency_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ExtendedGcdDependencyAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(
            MODULE.ExtendedGcdDependencyAuditResultError,
            "measured dependency result",
        ):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_xgcd_val_clear_is_rejected(self) -> None:
        self.reject(
            lambda value: next(
                row for row in value["rows"] if row["name"] == "Nat.xgcd_val"
            )["axiom_footprint"].clear()
        )

    def test_novel_dependency_removal_is_rejected(self) -> None:
        self.reject(lambda value: value["novel_candidate_dependencies"].pop())

    def test_reconstruction_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["summary"].__setitem__(
                "explicit_extended_gcd_reconstruction_authorized", True
            )
        )

    def test_export_claim_is_rejected(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("exporter_invocations", 1))

    def test_ledger_credit_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
