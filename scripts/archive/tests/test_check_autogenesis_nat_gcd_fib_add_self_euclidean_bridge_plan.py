from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-euclidean-bridge-plan.py"
SPEC = importlib.util.spec_from_file_location("euclidean_bridge_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanBridgePlanTests(unittest.TestCase):
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

    def test_same_name_transport_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("same_name_transport_allowed", True),
            "bridge authority",
        )

    def test_proof_body_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("proof_bodies_allowed", True),
            "bridge authority",
        )

    def test_target_submission_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_exact_source_target_submissions", 1),
            "bridge budget",
        )

    def test_retry_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_retries", 1),
            "bridge budget",
        )

    def test_equation_root_removal_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_stages"][0]["roots"].pop(),
            "fixed bridge stages",
        )

    def test_assumption_bearing_root_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_stages"][0].__setitem__(
                "required_footprint", ["propext"]
            ),
            "fixed bridge stages",
        )

    def test_target_reservation_change_is_rejected(self) -> None:
        self.reject(
            lambda value: value["target"].__setitem__("exact_target_submissions_reserved", 3),
            "target reservation",
        )


if __name__ == "__main__":
    unittest.main()
