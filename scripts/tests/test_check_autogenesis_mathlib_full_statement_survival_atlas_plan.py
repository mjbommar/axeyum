from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-mathlib-full-statement-survival-atlas-plan.py"
SPEC = importlib.util.spec_from_file_location("full_survival_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class FullStatementSurvivalAtlasPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.PlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_pretend_structural_observation_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observed_before_plan"].__setitem__(
                "structural_class_counts_observed", True
            ),
            "observed name boundary",
        )

    def test_second_pass_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_full_structural_comparisons", 2),
            "atlas budget",
        )

    def test_reselection_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("candidate_reselection_allowed", True),
            "atlas authority",
        )

    def test_projection_gate_removal_is_rejected(self) -> None:
        self.reject(
            lambda value: value["gates"].__setitem__(
                "selected_240_summary_must_equal_the_full_atlas_projection", False
            ),
            "atlas gates",
        )

    def test_retry_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_retries", 1),
            "atlas budget",
        )


if __name__ == "__main__":
    unittest.main()
