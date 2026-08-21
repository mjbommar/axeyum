from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-euclidean-subtraction-equation-addendum.py"
SPEC = importlib.util.spec_from_file_location("euclidean_sub_equation_addendum", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanSubtractionEquationAddendumTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.value = json.loads(MODULE.OUTPUT.read_text())

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.value)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.AddendumError, "addendum differs"):
            MODULE.validate(changed)

    def test_exact_addendum_is_accepted(self) -> None:
        MODULE.validate(self.value)

    def test_second_statement_is_rejected(self) -> None:
        self.reject(
            lambda value: value["use_scope"].__setitem__(
                "additional_statement_names_allowed", 1
            )
        )

    def test_proof_body_access_is_rejected(self) -> None:
        self.reject(
            lambda value: value["use_scope"].__setitem__("official_proof_may_be_read", True)
        )

    def test_footprint_gate_removal_is_rejected(self) -> None:
        self.reject(
            lambda value: value["use_scope"].__setitem__(
                "eventual_target_footprint_must_be_empty", False
            )
        )

    def test_submission_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("kernel_theorem_submissions", 1)
        )


if __name__ == "__main__":
    unittest.main()
