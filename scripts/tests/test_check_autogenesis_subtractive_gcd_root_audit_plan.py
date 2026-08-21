from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-subtractive-gcd-root-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("subtractive_gcd_root_audit_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SubtractiveGcdRootAuditPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.SubtractiveGcdAuditPlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_root_removal_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_roots"].pop(),
            "fixed proof-free gcd roots",
        )

    def test_batch_contract_change_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_measurement"].__setitem__(
                "root_order_must_match_plan", False
            ),
            "fixed batch measurement",
        )

    def test_bezout_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "subtractive_bezout_proof_allowed", True
            ),
            "audit authority",
        )

    def test_ledger_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("ledger_writes", 1),
            "audit authority",
        )


if __name__ == "__main__":
    unittest.main()
