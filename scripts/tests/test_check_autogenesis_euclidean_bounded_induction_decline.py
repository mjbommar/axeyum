from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-euclidean-bounded-induction-decline.py"
SPEC = importlib.util.spec_from_file_location(
    "euclidean_bounded_induction_decline", SCRIPT
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanBoundedInductionDeclineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.BoundedInductionDeclineError, message):
            MODULE.validate(changed)

    def test_exact_decline_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_empty_footprint_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"].__setitem__("axiom_footprint", []),
            "measured bounded-induction seam",
        )

    def test_generated_dependency_invention_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"][
                "generated_recursion_dependencies"
            ].append("Axeyum.Autogenesis.divAddModBoundedInduction._unary"),
            "measured bounded-induction seam",
        )

    def test_direct_dependency_removal_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"][
                "direct_theorem_dependencies"
            ].pop(),
            "measured bounded-induction seam",
        )

    def test_second_submission_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"].__setitem__(
                "second_submission_skipped", False
            ),
            "measured bounded-induction seam",
        )

    def test_acceptance_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"].__setitem__(
                "accepted_public_support", True
            ),
            "measured bounded-induction seam",
        )

    def test_ledger_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("ledger_writes", 1),
            "no-credit authority",
        )


if __name__ == "__main__":
    unittest.main()
