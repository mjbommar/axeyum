import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-imported-implementation-frontier.py"
SPEC = importlib.util.spec_from_file_location("implementation_frontier", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ImportedImplementationFrontierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.graph = json.loads(MODULE.GRAPH.read_text())
        cls.demand = json.loads(MODULE.DEMAND.read_text())

    def test_live_projection_replays_every_root(self):
        result = MODULE.build(self.graph, self.demand)
        self.assertEqual(result["census"]["transparent_structural_identities"], 1000)
        self.assertEqual(result["census"]["semantic_contract_roots"], 14)
        mod = [row for row in result["nodes"] if row["name"] == "Nat.mod"]
        self.assertTrue(mod)
        self.assertTrue(any(row["affected_targets"] >= 3 for row in mod))

    def test_missing_transparent_edge_fails_reachability_replay(self):
        graph = copy.deepcopy(self.graph)
        names = {node["node_id"]: node["name"] for node in graph["nodes"]}
        graph["edges"] = [
            edge
            for edge in graph["edges"]
            if not (
                names[edge["from_node_id"]] == "Nat.mod"
                and names[edge["to_node_id"]] == "Nat.modCore"
            )
        ]
        with self.assertRaisesRegex(ValueError, "reachability replay"):
            MODULE.build(graph, self.demand)

    def test_extra_semantic_root_fails_exact_join(self):
        demand = copy.deepcopy(self.demand)
        extra = copy.deepcopy(demand["demands"][0])
        extra["source_name"] = "Invented.definition"
        demand["demands"].append(extra)
        with self.assertRaisesRegex(ValueError, "roots and semantic demands"):
            MODULE.build(self.graph, demand)


if __name__ == "__main__":
    unittest.main()
