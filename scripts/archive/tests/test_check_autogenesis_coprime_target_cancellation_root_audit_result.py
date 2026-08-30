from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-coprime-target-cancellation-root-audit-result.py"
SPEC = importlib.util.spec_from_file_location("coprime_target_root_audit_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class CoprimeTargetRootAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(
            MODULE.CoprimeRootAuditResultError, "measured coprime root audit"
        ):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_shortcut_acceptance_is_rejected(self) -> None:
        self.reject(
            lambda value: value["summary"].__setitem__("accepted_target_route", True)
        )

    def test_quotient_footprint_removal_is_rejected(self) -> None:
        self.reject(
            lambda value: value["roots"][
                "Nat.Coprime.coprime_dvd_left"
            ].__setitem__("axiom_footprint", ["propext"])
        )

    def test_definition_equation_contamination_is_rejected(self) -> None:
        self.reject(
            lambda value: value["roots"]["Nat.Coprime.eq_1"].__setitem__(
                "axiom_footprint", ["propext"]
            )
        )

    def test_support_submission_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("new_theorem_submissions", 1)
        )

    def test_ledger_claim_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
