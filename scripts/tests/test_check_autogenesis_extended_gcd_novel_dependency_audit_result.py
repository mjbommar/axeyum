from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-extended-gcd-novel-dependency-audit-result.py"
SPEC = importlib.util.spec_from_file_location("extended_gcd_novel_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ExtendedGcdNovelDependencyAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(
            MODULE.ExtendedGcdNovelDependencyAuditResultError,
            "measured novel result",
        ):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_terminal_propext_removal_is_rejected(self) -> None:
        self.reject(
            lambda value: value["terminal_projection_equation"][
                "axiom_footprint"
            ].clear()
        )

    def test_clean_induction_contamination_is_rejected(self) -> None:
        self.reject(
            lambda value: value["clean_induction_interface"][
                "axiom_footprint"
            ].append("propext")
        )

    def test_imported_route_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["summary"].__setitem__(
                "imported_xgcd_route_open", True
            )
        )

    def test_reconstruction_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["summary"].__setitem__(
                "target_owned_reconstruction_authorized", True
            )
        )

    def test_ledger_credit_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
