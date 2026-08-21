from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-euclidean-local-subtraction-replacement-plan.py"
SPEC = importlib.util.spec_from_file_location("euclidean_local_sub_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanLocalSubtractionReplacementPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.ReplacementPlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_blocker_reselection_is_rejected(self) -> None:
        self.reject(
            lambda value: value["measured_blocker"].__setitem__("name", "dif_pos"),
            "measured blocker",
        )

    def test_global_helper_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_replacement"].__setitem__(
                "local_proof_may_create_a_global_declaration", True
            ),
            "fixed replacement",
        )

    def test_sub_add_cancel_reuse_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_replacement"].__setitem__(
                "forbidden_theorem_dependencies", []
            ),
            "fixed replacement",
        )

    def test_third_submission_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_kernel_theorem_submissions", 3),
            "replacement budget",
        )

    def test_public_lift_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "public_euclidean_lift_allowed", True
            ),
            "replacement authority",
        )


if __name__ == "__main__":
    unittest.main()
