from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-int-gcd-contract-theorem-control-policy.py"
SPEC = importlib.util.spec_from_file_location("check_int_gcd_contract_theorem_policy", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class IntGcdContractTheoremControlPolicyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.policy = MODULE.load(MODULE.POLICY)
        inputs = cls.policy["inputs"]
        cls.reviewed = MODULE.load(MODULE.ROOT / inputs["reviewed_nursery"]["path"])
        cls.contract = MODULE.load(MODULE.ROOT / inputs["source_contract_manifest"]["path"])
        fact_ids = [
            "F:ml430-int-fib-neg-b4021d37",
            "F:ml430-nat-fib-gcd-d1d98407",
            "F:ml430-int-gcd-fib-73bdafc2",
        ]
        cls.facts = {fact_id: MODULE.load(MODULE.fact_path(fact_id)) for fact_id in fact_ids}

    def reject(self, mutate, message):
        policy = copy.deepcopy(self.policy)
        mutate(policy)
        with self.assertRaisesRegex(MODULE.ControlPolicyError, message):
            MODULE.validate_policy(policy, self.reviewed, self.contract, self.facts)

    def test_exact_policy_is_accepted(self):
        MODULE.validate_policy(self.policy, self.reviewed, self.contract, self.facts)

    def test_calibration_cannot_claim_evaluation_credit(self):
        self.reject(
            lambda value: value["acceptance"].__setitem__("evaluation_credit", 1),
            "acceptance",
        )

    def test_budget_cannot_widen(self):
        self.reject(
            lambda value: value["producer"].__setitem__("max_retries", 1),
            "budget",
        )

    def test_execution_cannot_be_self_reported(self):
        self.reject(
            lambda value: value["authority"].__setitem__("producer_invocations_so_far", 1),
            "authority",
        )

    def test_horizon_premise_cannot_be_hidden(self):
        self.reject(
            lambda value: value["evaluation_horizon"].__setitem__("direct_premises", []),
            "dependency",
        )

    def test_held_out_access_cannot_be_enabled(self):
        self.reject(
            lambda value: value["authority"].__setitem__("held_out_allowed", True),
            "authority",
        )


if __name__ == "__main__":
    unittest.main()
