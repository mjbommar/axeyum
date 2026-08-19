from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-nat-fib-checked-theorem-receipt.py"
SPEC = importlib.util.spec_from_file_location("check_nat_fib_receipt", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class NatFibCheckedTheoremReceiptTests(unittest.TestCase):
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
        receipt["receipt_sha256"] = MODULE.digest(receipt_unsigned)
        unsigned = dict(observation)
        unsigned.pop("observation_sha256", None)
        observation["observation_sha256"] = MODULE.digest(unsigned)
        with self.assertRaisesRegex(MODULE.FibReceiptError, message):
            MODULE.validate_observation(observation)

    def test_exact_receipt_is_accepted(self):
        MODULE.validate_observation(self.observation)

    def test_axiom_is_rejected(self):
        self.reject(
            lambda value: value["semantic_theorem_receipt"]["axiom_footprint"].append(
                "Answer"
            ),
            "receipt changed",
        )

    def test_search_is_rejected(self):
        self.reject(
            lambda value: value["assurance"].__setitem__("search_invocations", 1),
            "assurance",
        )

    def test_candidate_substitution_is_rejected(self):
        self.reject(
            lambda value: value.__setitem__("candidate_observation_sha256", "0" * 64),
            "contract",
        )

    def test_credit_is_rejected(self):
        self.reject(
            lambda value: value["authority"].__setitem__("evaluation_credit", 1),
            "authority",
        )


if __name__ == "__main__":
    unittest.main()
