from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-euclidean-public-lift-decline.py"
SPEC = importlib.util.spec_from_file_location("euclidean_public_lift_decline", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanPublicLiftDeclineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.PublicLiftDeclineError, message):
            MODULE.validate(changed)

    def test_exact_decline_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_transparency_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"].__setitem__(
                "nat_div_is_transparent_to_elaborator", True
            ),
            "opaque division seam",
        )

    def test_bridge_invention_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"][
                "proof_free_div_go_to_public_div_bridge_statements"
            ].append("invented"),
            "opaque division seam",
        )

    def test_kernel_submission_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("kernel_theorem_submissions", 1),
            "zero-submission boundary",
        )

    def test_acceptance_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"].__setitem__(
                "accepted_public_support", True
            ),
            "opaque division seam",
        )

    def test_evaluation_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("evaluation_credit", 1),
            "no-credit authority",
        )


if __name__ == "__main__":
    unittest.main()
