from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-support-plan.py"
SPEC = importlib.util.spec_from_file_location("check_nat_gcd_fib_add_self_support_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class NatGcdFibAddSelfSupportPlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.PlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_support_reordering_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_plan"]["support_order"].reverse(),
            "construction",
        )

    def test_target_step_skip_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_plan"]["target_construction"]["successor_steps"].pop(),
            "construction",
        )

    def test_budget_widening_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_retries", 1),
            "budget",
        )

    def test_target_before_support_is_rejected(self) -> None:
        self.reject(
            lambda value: value["gates"].__setitem__("support_before_target", False),
            "gates",
        )

    def test_proof_body_or_admission_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("proof_bodies_allowed", True),
            "authority",
        )
        self.reject(
            lambda value: value["authority"].__setitem__("admission_allowed", True),
            "authority",
        )


if __name__ == "__main__":
    unittest.main()
