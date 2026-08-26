import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-imported-implementation-demand.py"
SPEC = importlib.util.spec_from_file_location("implementation_demand", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ImportedImplementationDemandTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(MODULE.ARTIFACT.read_text())
        cls.replay = json.loads(MODULE.REPLAY.read_text())
        cls.demand = json.loads(MODULE.SEMANTIC_DEMAND.read_text())

    def test_live_artifact(self):
        census = MODULE.validate(self.data, self.replay, self.demand)
        self.assertEqual(census["root_definition_identities"], 14)

    def test_missing_modulus_edge_fails_closed(self):
        data = copy.deepcopy(self.data)
        names = {node["node_id"]: node["name"] for node in data["nodes"]}
        data["edges"] = [
            edge
            for edge in data["edges"]
            if not (
                names[edge["from_node_id"]] == "Nat.mod"
                and names[edge["to_node_id"]] == "Nat.modCore"
            )
        ]
        data["census"]["distinct_direct_edges"] = len(data["edges"])
        with self.assertRaisesRegex(ValueError, "Nat.mod"):
            MODULE.validate(data, self.replay, self.demand)

    def test_extra_root_fails_exact_join(self):
        data = copy.deepcopy(self.data)
        data["roots"].append(copy.deepcopy(data["roots"][0]))
        data["roots"][-1]["source_name"] = "Invented.definition"
        with self.assertRaisesRegex(ValueError, "exactly match"):
            MODULE.validate(data, self.replay, self.demand)


if __name__ == "__main__":
    unittest.main()
