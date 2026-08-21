from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-euclidean-local-subtraction-replacement-result.py"
SPEC = importlib.util.spec_from_file_location("euclidean_local_sub_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanLocalSubtractionReplacementResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.ReplacementResultError, message):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_footprint_injection_is_rejected(self) -> None:
        self.reject(
            lambda value: value["theorem"].__setitem__("axiom_footprint", ["propext"]),
            "accepted theorem",
        )

    def test_forbidden_dependency_is_rejected(self) -> None:
        self.reject(
            lambda value: value["theorem"]["direct_theorem_dependencies"].append(
                "Nat.sub_add_cancel"
            ),
            "accepted theorem",
        )

    def test_second_reconstruction_erasure_is_rejected(self) -> None:
        self.reject(
            lambda value: value["theorem"].__setitem__("fresh_reconstructions", 1),
            "accepted theorem",
        )

    def test_public_lift_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "public_euclidean_lift_submissions", 1
            ),
            "private-support authority",
        )

    def test_target_submission_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("exact_target_submissions", 1),
            "reconstruction budget",
        )


if __name__ == "__main__":
    unittest.main()
