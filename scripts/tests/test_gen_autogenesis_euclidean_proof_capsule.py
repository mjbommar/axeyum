from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-euclidean-proof-capsule.py"
SPEC = importlib.util.spec_from_file_location("euclidean_proof_capsule", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanProofCapsuleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.capsule = json.loads(MODULE.OUTPUT.read_text())

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.capsule)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.CapsuleError, "capsule differs"):
            MODULE.validate_capsule(changed)

    def test_exact_capsule_is_accepted(self) -> None:
        MODULE.validate_capsule(self.capsule)

    def test_statement_removal_is_rejected(self) -> None:
        self.reject(lambda value: value["allowed_statements"].pop())

    def test_proof_stream_textual_access_is_rejected(self) -> None:
        self.reject(
            lambda value: value["proof_bearing_kernel_input"].__setitem__(
                "textual_read_allowed", True
            )
        )

    def test_proof_body_input_is_rejected(self) -> None:
        self.reject(
            lambda value: value["isolation_policy"]["allowed_inputs"].append(
                "upstream proof body"
            )
        )

    def test_target_submission_is_rejected(self) -> None:
        self.reject(
            lambda value: value["construction_contract"].__setitem__(
                "exact_target_submissions", 1
            )
        )

    def test_nonempty_footprint_is_rejected(self) -> None:
        self.reject(
            lambda value: value["construction_contract"]["required_axiom_footprint"].append(
                "propext"
            )
        )

    def test_credit_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("evaluation_credit", 1))


if __name__ == "__main__":
    unittest.main()
