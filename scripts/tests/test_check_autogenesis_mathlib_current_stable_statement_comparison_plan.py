from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-mathlib-current-stable-statement-comparison-plan.py"
SPEC = importlib.util.spec_from_file_location("stable_statement_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class StableStatementComparisonPlanTests(unittest.TestCase):
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

    def test_prerelease_is_rejected(self) -> None:
        self.reject(
            lambda value: value["comparison"].__setitem__("mathlib_tag", "v4.33.0-rc1"),
            "comparison release",
        )

    def test_extractor_patch_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_extractor_compatibility_patches", 1),
            "comparison budget",
        )

    def test_proof_body_access_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "mathlib_source_proof_bodies_allowed", True
            ),
            "comparison authority",
        )

    def test_candidate_count_change_is_rejected(self) -> None:
        self.reject(
            lambda value: value["inputs"]["selected_candidates"].__setitem__(
                "records", 239
            ),
            "selected candidate count",
        )

    def test_retry_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_retries", 1),
            "comparison budget",
        )

    def test_fact_change_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("fact_status_changes_allowed", True),
            "comparison authority",
        )


if __name__ == "__main__":
    unittest.main()
