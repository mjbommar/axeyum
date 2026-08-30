from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-xgcd-val-rooted-reconstruction-plan.py"
SPEC = importlib.util.spec_from_file_location("xgcd_val_rooted_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class XgcdValRootedReconstructionPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.XgcdValRootedPlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_cleanup_expansion_is_rejected(self) -> None:
        self.reject(
            lambda value: value["execution"].__setitem__(
                "cleanup_scope_is_exactly_the_three_named_paths", False
            ),
            "execution or cleanup boundary",
        )

    def test_dirty_after_state_is_rejected(self) -> None:
        self.reject(
            lambda value: value["execution"].__setitem__(
                "mathlib_status_entries_after_cleanup", 1
            ),
            "execution or cleanup boundary",
        )

    def test_export_before_compile_is_rejected(self) -> None:
        self.reject(
            lambda value: value["execution"].__setitem__(
                "export_only_after_successful_compilation", False
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
