from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-generated-gcd-novel-dependency-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("generated_gcd_novel_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class GeneratedGcdNovelDependencyAuditPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.GeneratedGcdNovelDependencyAuditPlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_root_change_is_rejected(self) -> None:
        self.reject(lambda value: value["fixed_roots"].pop(), "fixed derived roots")

    def test_import_budget_change_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_batch_importer_runs", 2),
            "audit budget",
        )

    def test_reconstruction_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("reconstruction_allowed", True),
            "audit authority",
        )

    def test_success_rule_change_is_rejected(self) -> None:
        self.reject(
            lambda value: value["decision_rule"].__setitem__(
                "only_generic_fix_equation_may_remain_assumption_bearing", False
            ),
            "decision rule",
        )


if __name__ == "__main__":
    unittest.main()
