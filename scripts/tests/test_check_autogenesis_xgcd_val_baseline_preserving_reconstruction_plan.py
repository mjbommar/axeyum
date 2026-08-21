from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-xgcd-val-baseline-preserving-reconstruction-plan.py"
SPEC = importlib.util.spec_from_file_location("xgcd_val_baseline_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class XgcdValBaselinePreservingPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.XgcdValBaselinePlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_baseline_hash_change_is_rejected(self) -> None:
        self.reject(
            lambda value: value["preexisting_status_baseline"][0].__setitem__(
                "sha256", "0" * 64
            ),
            "preexisting baseline",
        )

    def test_baseline_mutation_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "preexisting_files_may_be_changed_or_removed", True
            ),
            "authority changed",
        )

    def test_cleanup_expansion_is_rejected(self) -> None:
        self.reject(
            lambda value: value["execution"].__setitem__(
                "cleanup_scope_is_exactly_the_three_named_paths", False
            ),
            "execution or cleanup boundary",
        )

    def test_retry_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_retries", 1),
            "budget changed",
        )

    def test_projection_credit_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "projection_equation_credit", 1
            ),
            "authority changed",
        )


if __name__ == "__main__":
    unittest.main()
