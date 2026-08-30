from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-xgcd-val-direct-reconstruction-plan.py"
SPEC = importlib.util.spec_from_file_location("xgcd_val_direct_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class XgcdValDirectReconstructionPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.XgcdValDirectPlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_target_change_is_rejected(self) -> None:
        self.reject(
            lambda value: value["target"].__setitem__("name", "Nat.xgcd.eq_1"),
            "frontier, source, or target identity",
        )

    def test_simp_is_rejected(self) -> None:
        self.reject(
            lambda value: value["construction"].__setitem__(
                "proof_search_allowed", True
            ),
            "construction changed",
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

    def test_single_import_is_rejected(self) -> None:
        self.reject(
            lambda value: value["acceptance"].__setitem__(
                "fresh_kernel_imports_required", 1
            ),
            "acceptance changed",
        )


if __name__ == "__main__":
    unittest.main()
