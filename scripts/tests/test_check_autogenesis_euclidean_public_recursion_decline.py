from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-euclidean-public-recursion-decline.py"
SPEC = importlib.util.spec_from_file_location(
    "euclidean_public_recursion_decline", SCRIPT
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanPublicRecursionDeclineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.PublicRecursionDeclineError, message):
            MODULE.validate(changed)

    def test_exact_decline_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_empty_footprint_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"].__setitem__("axiom_footprint", []),
            "measured recursion seam",
        )

    def test_generated_dependency_removal_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"].__setitem__(
                "direct_theorem_dependencies", []
            ),
            "measured recursion seam",
        )

    def test_second_submission_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"].__setitem__(
                "second_submission_skipped", False
            ),
            "measured recursion seam",
        )

    def test_acceptance_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"].__setitem__(
                "accepted_public_support", True
            ),
            "measured recursion seam",
        )

    def test_target_submission_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__(
                "exact_fibonacci_target_submissions", 1
            ),
            "first-decline budget",
        )

    def test_evaluation_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("evaluation_credit", 1),
            "no-credit authority",
        )


if __name__ == "__main__":
    unittest.main()
