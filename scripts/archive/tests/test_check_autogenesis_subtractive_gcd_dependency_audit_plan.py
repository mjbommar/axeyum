from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-subtractive-gcd-dependency-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("subtractive_gcd_dependency_audit_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SubtractiveGcdDependencyAuditPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.SubtractiveGcdDependencyAuditPlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_root_removal_is_rejected(self) -> None:
        self.reject(lambda value: value["fixed_roots"].pop(), "fixed derived roots")

    def test_export_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_exporter_invocations", 1),
            "audit budget",
        )

    def test_replacement_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("replacement_proof_allowed", True),
            "audit authority",
        )

    def test_unmeasured_reconstruction_is_rejected(self) -> None:
        self.reject(
            lambda value: value["decision_rule"].__setitem__(
                "next_plan_may_reconstruct_only_measured_assumption_carriers", False
            ),
            "successor rule",
        )


if __name__ == "__main__":
    unittest.main()
