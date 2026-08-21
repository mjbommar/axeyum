from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-coprime-target-cancellation-root-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("coprime_target_root_audit_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class CoprimeTargetRootAuditPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.CoprimeRootAuditPlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_root_removal_is_rejected(self) -> None:
        self.reject(lambda value: value["fixed_roots"].pop(), "fixed proof-free roots")

    def test_export_budget_expansion_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_exporter_invocations", 2),
            "audit budget",
        )

    def test_proof_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "target_cancellation_proof_allowed", True
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
