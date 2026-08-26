import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-semantic-contract-demand.py"
SPEC = importlib.util.spec_from_file_location("semantic_contract_demand", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SemanticContractDemandTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.replay = json.loads(MODULE.REPLAY.read_text())
        cls.index = json.loads(MODULE.LEMMA_INDEX.read_text())

    def test_live_join_selects_testbit_first(self):
        result = MODULE.build(self.replay, self.index)
        self.assertEqual(result["census"]["distinct_source_identities"], 14)
        self.assertEqual(result["census"]["identities_with_checked_contract_receipts"], 0)
        self.assertEqual(result["census"]["identities_with_exact_kernel_candidates"], 2)
        self.assertEqual(result["census"]["exact_axiom_free_kernel_candidates"], 11)
        self.assertEqual(result["demands"][0]["source_name"], "Nat.testBit")
        self.assertEqual(result["demands"][0]["affected_targets"], 4)
        self.assertEqual(result["demands"][0]["exact_axiom_free_kernel_candidate_count"], 5)

    def test_nonaccepted_slice_fails_closed(self):
        replay = copy.deepcopy(self.replay)
        replay["rows"][0]["outcome"] = "declined"
        with self.assertRaisesRegex(ValueError, "non-accepted"):
            MODULE.build(replay, self.index)

    def test_assumption_bearing_candidate_is_excluded(self):
        index = copy.deepcopy(self.index)
        testbit = next(
            row
            for row in index["lemmas"]
            if "Nat.testBit" in row["direct_type_dependencies"]
        )
        testbit["axiom_footprint_size"] = 1
        result = MODULE.build(self.replay, index)
        demand = next(
            row for row in result["demands"] if row["source_name"] == "Nat.testBit"
        )
        self.assertEqual(demand["exact_axiom_free_kernel_candidate_count"], 4)


if __name__ == "__main__":
    unittest.main()
