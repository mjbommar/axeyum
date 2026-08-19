from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-nat-fib-gcd-premise-selection-policy.py"
SPEC = importlib.util.spec_from_file_location("check_nat_fib_gcd_premise_policy", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class NatFibGcdPremiseSelectionPolicyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.policy = MODULE.load(MODULE.POLICY)
        cls.reviewed = MODULE.load(MODULE.ROOT / cls.policy["inputs"]["reviewed_nursery"]["path"])
        fact_ids = [row["fact_id"] for row in cls.policy["bottom_up_chain"]]
        fact_ids += cls.policy["strategic_choice"]["selected_direct_unlocks"]
        cls.facts = {fact_id: MODULE.load(MODULE.fact_path(fact_id)) for fact_id in set(fact_ids)}

    def reject(self, mutate, message):
        policy = copy.deepcopy(self.policy)
        mutate(policy)
        with self.assertRaisesRegex(MODULE.PremiseSelectionError, message):
            MODULE.validate_policy(policy, self.reviewed, self.facts)

    def test_exact_policy_is_accepted(self):
        MODULE.validate_policy(self.policy, self.reviewed, self.facts)

    def test_target_swap_is_rejected(self):
        self.reject(lambda value: value["strategic_choice"].__setitem__("selected", "Int.fib_neg"), "strategic")

    def test_chain_skip_is_rejected(self):
        self.reject(lambda value: value["bottom_up_chain"].pop(1), "sequence")

    def test_budget_widening_is_rejected(self):
        self.reject(lambda value: value["producer"].__setitem__("max_kernel_submissions", 3), "budget")

    def test_proof_body_access_is_rejected(self):
        self.reject(lambda value: value["producer"].__setitem__("proof_bodies_allowed", True), "budget")

    def test_execution_credit_is_rejected(self):
        self.reject(lambda value: value["authority"].__setitem__("evaluation_credit_so_far", 1), "authority")


if __name__ == "__main__":
    unittest.main()
