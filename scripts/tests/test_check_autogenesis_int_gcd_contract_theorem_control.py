from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-int-gcd-contract-theorem-control.py"
SPEC = importlib.util.spec_from_file_location("check_int_gcd_contract_theorem_control", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class IntGcdContractTheoremControlTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = MODULE.load(MODULE.MANIFEST)
        archive = cls.manifest["observation_archive"]
        cls.observation = MODULE.load(Path(archive["root"]) / archive["file"])

    def reject(self, mutate, message):
        observation = copy.deepcopy(self.observation)
        mutate(observation)
        receipt = observation["semantic_theorem_receipt"]
        receipt_unsigned = dict(receipt)
        receipt_unsigned.pop("receipt_sha256", None)
        receipt["receipt_sha256"] = MODULE.canonical_digest(receipt_unsigned)
        observation_unsigned = dict(observation)
        observation_unsigned.pop("observation_sha256", None)
        observation["observation_sha256"] = MODULE.canonical_digest(observation_unsigned)
        with self.assertRaisesRegex(MODULE.ContractTheoremControlError, message):
            MODULE.validate_observation(observation)

    def test_exact_control_is_accepted(self):
        MODULE.validate_observation(self.observation)

    def test_evaluation_credit_is_rejected(self):
        self.reject(
            lambda value: value["authority"].__setitem__("evaluation_credit", 1),
            "authority",
        )

    def test_second_invocation_is_rejected(self):
        self.reject(
            lambda value: value["assurance"].__setitem__("producer_invocations", 2),
            "authority",
        )

    def test_axiom_is_rejected(self):
        self.reject(
            lambda value: value["semantic_theorem_receipt"].__setitem__(
                "axiom_footprint", ["Answer"]
            ),
            "receipt identity",
        )

    def test_source_receipt_substitution_is_rejected(self):
        self.reject(
            lambda value: value.__setitem__("source_contract_receipt_sha256", "0" * 64),
            "authority",
        )

    def test_dependency_authority_relabel_is_rejected(self):
        self.reject(
            lambda value: value["assurance"].__setitem__(
                "dependency_inventory_is_diagnostic_only", False
            ),
            "authority",
        )


if __name__ == "__main__":
    unittest.main()
