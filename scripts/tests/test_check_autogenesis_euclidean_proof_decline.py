from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-euclidean-proof-decline.py"
SPEC = importlib.util.spec_from_file_location("euclidean_proof_decline", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanProofDeclineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.DeclineError, message):
            MODULE.validate(changed)

    def test_exact_decline_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_empty_footprint_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"].__setitem__("axiom_footprint", []),
            "measured theorem decline",
        )

    def test_second_run_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("second_reconstruction_run", True),
            "stop boundary",
        )

    def test_accepted_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["observation"].__setitem__("accepted", True),
            "measured theorem decline",
        )

    def test_target_submission_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("exact_target_submissions", 1),
            "stop boundary",
        )

    def test_evaluation_credit_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("evaluation_credit", 1),
            "no-credit authority",
        )


if __name__ == "__main__":
    unittest.main()
