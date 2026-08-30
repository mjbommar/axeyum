from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-support-result.py"
SPEC = importlib.util.spec_from_file_location("check_nat_gcd_fib_add_self_support_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class NatGcdFibAddSelfSupportResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)
        archive = pathlib.Path(cls.result["reference_pack"]["root"])
        cls.manifest = MODULE.load(archive / cls.result["reference_pack"]["manifest"])
        cls.observation = MODULE.load(archive / cls.manifest["observations"][0]["file"])

    def reject_result(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.SupportResultError, message):
            MODULE.validate(changed)

    def reject_manifest(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.manifest)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.SupportResultError, message):
            MODULE.validate_manifest(changed)

    def reject_observation(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.observation)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.SupportResultError, message):
            MODULE.validate_observation(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_second_support_credit_is_rejected(self) -> None:
        self.reject_result(
            lambda value: value["result"].__setitem__("support_theorems_reconstructed", 2),
            "bounded result",
        )

    def test_target_submission_is_rejected(self) -> None:
        self.reject_observation(
            lambda value: value.__setitem__("exact_source_target_submissions", 1),
            "observation contract",
        )

    def test_axiom_footprint_is_rejected(self) -> None:
        self.reject_observation(
            lambda value: value["supports"][0]["axiom_footprint"].append("Classical.choice"),
            "observation contract",
        )

    def test_dependency_substitution_is_rejected(self) -> None:
        self.reject_observation(
            lambda value: value["supports"][0]["direct_theorem_dependencies"].pop(),
            "observation contract",
        )

    def test_reconstruction_count_is_rejected(self) -> None:
        self.reject_observation(
            lambda value: value["supports"][0].__setitem__("fresh_reconstructions", 1),
            "observation contract",
        )

    def test_composition_receipt_substitution_is_rejected(self) -> None:
        self.reject_observation(
            lambda value: value.__setitem__("addition_composition_receipt_sha256", "0" * 64),
            "composition receipt",
        )

    def test_target_boundary_credit_is_rejected(self) -> None:
        self.reject_manifest(
            lambda value: value["target_boundary"].__setitem__("epistemic_status", "proved"),
            "target boundary",
        )

    def test_evaluation_credit_is_rejected(self) -> None:
        self.reject_manifest(
            lambda value: value["authority"].__setitem__("evaluation_credit", 1),
            "authority",
        )


class NatGcdFibAddSelfSupportResultV2Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT_V2)
        archive = pathlib.Path(cls.result["reference_pack"]["root"])
        cls.manifest = MODULE.load(archive / cls.result["reference_pack"]["manifest"])
        cls.observation = MODULE.load(archive / cls.manifest["observations"][0]["file"])

    def reject_result(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.SupportResultError, message):
            MODULE.validate_v2(changed)

    def reject_manifest(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.manifest)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.SupportResultError, message):
            MODULE.validate_manifest_v2(changed)

    def reject_observation(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.observation)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.SupportResultError, message):
            MODULE.validate_observation_v2(changed)

    def test_exact_v2_result_is_accepted(self) -> None:
        MODULE.validate_v2(self.result)

    def test_axiom_is_rejected(self) -> None:
        self.reject_observation(
            lambda value: value["supports"][1]["axiom_footprint"].append("Quot.sound"),
            "v2 observation",
        )

    def test_dependency_removal_is_rejected(self) -> None:
        self.reject_observation(
            lambda value: value["supports"][1]["direct_theorem_dependencies"].pop(),
            "v2 observation",
        )

    def test_fake_target_portability_is_rejected(self) -> None:
        self.reject_manifest(
            lambda value: value["target_composition"].__setitem__("accepted", True),
            "v2 reference manifest",
        )

    def test_native_transport_authority_is_rejected(self) -> None:
        self.reject_result(
            lambda value: value["failure"].__setitem__("native_transport_authorized", True),
            "v2 result identity",
        )

    def test_target_submission_is_rejected(self) -> None:
        self.reject_observation(
            lambda value: value.__setitem__("exact_source_target_submissions", 1),
            "v2 observation",
        )

    def test_proof_body_inspection_is_rejected(self) -> None:
        self.reject_manifest(
            lambda value: value["statement_only_horizon"].__setitem__(
                "proof_bodies_inspected", True
            ),
            "statement-only horizon",
        )


if __name__ == "__main__":
    unittest.main()
