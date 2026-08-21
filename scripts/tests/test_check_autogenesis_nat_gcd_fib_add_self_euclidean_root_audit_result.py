from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-euclidean-root-audit-result.py"
SPEC = importlib.util.spec_from_file_location("euclidean_root_audit", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanRootAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)
        pack = pathlib.Path(cls.result["reference_pack"]["root"])
        cls.manifest = MODULE.load(pack / cls.result["reference_pack"]["manifest"])

    def reject_result(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.ResultError, message):
            MODULE.validate(changed)

    def reject_manifest(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.manifest)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.ResultError, message):
            MODULE.validate_manifest(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_axiom_is_rejected(self) -> None:
        self.reject_result(
            lambda value: value["roots"]["Nat.div.go.eq_1"]["axiom_footprint"].append("propext"),
            "result contract",
        )

    def test_root_removal_is_rejected(self) -> None:
        self.reject_manifest(
            lambda value: value["generation"]["roots"].pop(),
            "reference manifest",
        )

    def test_proof_body_display_is_rejected(self) -> None:
        self.reject_manifest(
            lambda value: value["generation"].__setitem__("proof_bodies_displayed", True),
            "reference manifest",
        )

    def test_support_submission_is_rejected(self) -> None:
        self.reject_manifest(
            lambda value: value["authority"].__setitem__(
                "authored_support_theorem_submissions", 1
            ),
            "reference manifest",
        )

    def test_target_submission_is_rejected(self) -> None:
        self.reject_result(
            lambda value: value["counters"].__setitem__("exact_source_target_submissions", 1),
            "result contract",
        )


if __name__ == "__main__":
    unittest.main()
