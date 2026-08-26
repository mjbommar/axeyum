import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-bit-observation-contract-slice.py"
SPEC = importlib.util.spec_from_file_location("bit_contract_slice", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BitObservationContractSliceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.graph = json.loads(MODULE.GRAPH.read_text())
        cls.replay = json.loads(MODULE.REPLAY.read_text())
        cls.demand = json.loads(MODULE.DEMAND.read_text())

    def test_live_family_is_exactly_four_targets(self):
        result = MODULE.build(self.graph, self.replay, self.demand)
        self.assertEqual(result["census"]["targets"], 4)
        self.assertEqual(result["census"]["exact_axiom_free_behavior_candidates"], 5)
        self.assertIn("Nat.testBit", {row["name"] for row in result["observation_focus"]})

    def test_missing_affected_replay_row_fails(self):
        replay = copy.deepcopy(self.replay)
        replay["rows"] = [
            row
            for row in replay["rows"]
            if row["fact_id"] != self.demand["demands"][0]["affected_fact_ids"][0]
        ]
        with self.assertRaisesRegex(ValueError, "no checked type slice"):
            MODULE.build(self.graph, replay, self.demand)

    def test_family_size_drift_fails(self):
        demand = copy.deepcopy(self.demand)
        row = next(row for row in demand["demands"] if row["source_name"] == "Nat.testBit")
        row["affected_targets"] = 3
        with self.assertRaisesRegex(ValueError, "reviewed four-target"):
            MODULE.build(self.graph, self.replay, demand)


if __name__ == "__main__":
    unittest.main()
