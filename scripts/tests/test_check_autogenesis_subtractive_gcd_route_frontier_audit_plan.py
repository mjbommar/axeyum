from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-subtractive-gcd-route-frontier-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("subtractive_gcd_route_frontier_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SubtractiveGcdRouteFrontierAuditPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.SubtractiveGcdRouteFrontierAuditPlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_subtraction_is_not_reaudited(self) -> None:
        self.reject(
            lambda value: value["fixed_roots"].append("Nat.sub_add_cancel"),
            "fixed derived roots",
        )

    def test_export_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_exporter_invocations", 1),
            "audit budget",
        )

    def test_replacement_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("replacement_proof_allowed", True),
            "audit authority",
        )

    def test_decision_rule_weakening_is_rejected(self) -> None:
        self.reject(
            lambda value: value["decision_rule"].__setitem__(
                "assumption_bearing_divisibility_roots_require_further_measurement_or_local_replacement",
                False,
            ),
            "decision rule",
        )


if __name__ == "__main__":
    unittest.main()
