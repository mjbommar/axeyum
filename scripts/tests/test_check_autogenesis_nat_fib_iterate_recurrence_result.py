from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-nat-fib-iterate-recurrence-result.py"
SPEC = importlib.util.spec_from_file_location("check_nat_fib_iterate_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class NatFibIterateRecurrenceResultTests(unittest.TestCase):
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
        with self.assertRaisesRegex(MODULE.IterateRecurrenceResultError, message):
            MODULE.validate_observation(observation)

    def test_exact_negative_result_is_accepted(self):
        MODULE.validate_observation(self.observation)

    def test_retry_is_rejected(self):
        self.reject(
            lambda value: value["execution"].__setitem__("producer_retries", 1),
            "negative execution",
        )

    def test_kernel_acceptance_is_rejected(self):
        self.reject(
            lambda value: value["execution"].__setitem__("kernel_accepted", True),
            "negative execution",
        )

    def test_evaluation_credit_is_rejected(self):
        self.reject(
            lambda value: value["authority"].__setitem__("evaluation_credit", 1),
            "authority",
        )

    def test_target_preflight_is_rejected(self):
        self.reject(
            lambda value: value["preflight"].__setitem__("target_submissions", 1),
            "preflight",
        )

    def test_rejection_substitution_is_rejected(self):
        self.reject(
            lambda value: value["execution"].__setitem__("rejection", "accepted"),
            "negative execution",
        )


class NatFibIterateRecurrenceV2ResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = MODULE.load(MODULE.MANIFEST_V2)
        archive = cls.manifest["observation_archive"]
        cls.observation = MODULE.load(Path(archive["root"]) / archive["file"])

    def reject(self, mutate, message):
        observation = copy.deepcopy(self.observation)
        mutate(observation)
        unsigned = dict(observation)
        unsigned.pop("observation_sha256", None)
        observation["observation_sha256"] = MODULE.canonical_digest(unsigned)
        with self.assertRaisesRegex(MODULE.IterateRecurrenceResultError, message):
            MODULE.validate_observation_v2(observation)

    def test_exact_v2_negative_result_is_accepted(self):
        MODULE.validate_observation_v2(self.observation)

    def test_v2_retry_is_rejected(self):
        self.reject(
            lambda value: value["execution"].__setitem__("producer_retries", 1),
            "v2 negative execution",
        )

    def test_v2_fake_acceptance_is_rejected(self):
        self.reject(
            lambda value: value["execution"].__setitem__("kernel_accepted", True),
            "v2 negative execution",
        )

    def test_v2_target_bearing_control_is_rejected(self):
        self.reject(
            lambda value: value["preexecution_controls"].__setitem__(
                "target_submissions", 1
            ),
            "v2 preexecution controls",
        )

    def test_v2_credit_is_rejected(self):
        self.reject(
            lambda value: value["authority"].__setitem__("evaluation_credit", 1),
            "v2 observation authority",
        )


if __name__ == "__main__":
    unittest.main()
