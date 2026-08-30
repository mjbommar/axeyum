from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-nat-fib-recurrence-v3-result.py"
SPEC = importlib.util.spec_from_file_location("check_nat_fib_v3", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class NatFibRecurrenceV3ResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = MODULE.load(MODULE.MANIFEST)
        archive = cls.manifest["observation_archive"]
        cls.observation = MODULE.load(Path(archive["root"]) / archive["file"])

    def reject(self, mutate, message):
        observation = copy.deepcopy(self.observation)
        mutate(observation)
        unsigned = dict(observation)
        unsigned.pop("observation_sha256", None)
        observation["observation_sha256"] = MODULE.canonical_digest(unsigned)
        with self.assertRaisesRegex(MODULE.FibV3ResultError, message):
            MODULE.validate_observation(observation)

    def test_exact_candidate_is_accepted(self):
        MODULE.validate_observation(self.observation)

    def test_axiom_is_rejected(self):
        self.reject(
            lambda value: value["candidate"]["axiom_footprint"].append("Answer"),
            "candidate",
        )

    def test_retry_is_rejected(self):
        self.reject(
            lambda value: value["search"].__setitem__("retries", 1),
            "search",
        )

    def test_fake_receipt_is_rejected(self):
        self.reject(
            lambda value: value["authority"].__setitem__(
                "semantic_theorem_receipts_issued", 1
            ),
            "authority",
        )

    def test_evaluation_credit_is_rejected(self):
        self.reject(
            lambda value: value["authority"].__setitem__("evaluation_credit", 1),
            "authority",
        )

    def test_proof_substitution_is_rejected(self):
        self.reject(
            lambda value: value["candidate"].__setitem__("proof_sha256", "0" * 64),
            "candidate",
        )


if __name__ == "__main__":
    unittest.main()
