from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-nat-gcd-greatest-plan.py"
SPEC = importlib.util.spec_from_file_location("check_nat_gcd_greatest_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class NatGcdGreatestPlanTests(unittest.TestCase):
    def setUp(self):
        self.plan = MODULE.load(MODULE.PLAN)

    def test_exact_plan_is_accepted(self):
        MODULE.validate(self.plan)

    def test_target_swap_is_rejected(self):
        changed = copy.deepcopy(self.plan)
        changed["target"]["name"] = "Nat.gcd_greatest_wrong"
        with self.assertRaisesRegex(MODULE.PlanError, "target"):
            MODULE.validate(changed)

    def test_dependency_removal_is_rejected(self):
        changed = copy.deepcopy(self.plan)
        changed["required_direct_theorem_dependencies"].pop()
        with self.assertRaisesRegex(MODULE.PlanError, "dependency"):
            MODULE.validate(changed)

    def test_budget_widening_is_rejected(self):
        changed = copy.deepcopy(self.plan)
        changed["budget"]["max_retries"] = 1
        with self.assertRaisesRegex(MODULE.PlanError, "budget"):
            MODULE.validate(changed)

    def test_axiom_footprint_acceptance_cannot_widen(self):
        changed = copy.deepcopy(self.plan)
        changed["acceptance"]["all_axiom_footprints"] = ["propext"]
        with self.assertRaisesRegex(MODULE.PlanError, "acceptance"):
            MODULE.validate(changed)


if __name__ == "__main__":
    unittest.main()
