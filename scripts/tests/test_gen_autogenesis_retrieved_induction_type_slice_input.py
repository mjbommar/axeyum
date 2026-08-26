import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-retrieved-induction-type-slice-input.py"
SPEC = importlib.util.spec_from_file_location("type_slice_input", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class RetrievedInductionTypeSliceInputTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.projection = json.loads(MODULE.PROJECTION.read_text())
        cls.nursery = json.loads(MODULE.NURSERY.read_text())

    def test_live_population_is_exact_and_unsealed(self):
        result = MODULE.build(self.projection, self.nursery)
        self.assertEqual(len(result["rows"]), 25)
        self.assertEqual(result["authority"]["facts_opened"], 25)
        self.assertFalse(result["authority"]["held_out_inspected"])
        self.assertTrue(result["authority"]["target_outcomes_accessed"])
        self.assertEqual(
            {row["partition"] for row in result["rows"]},
            {"train", "development"},
        )

    def test_control_cannot_enter_through_a_demand_mutation(self):
        projection = copy.deepcopy(self.projection)
        control = copy.deepcopy(projection["control_observations"][0])
        control["capability_demand"] = "type-slice-generalization"
        projection["strategy_queue"].append(control)
        with self.assertRaisesRegex(ValueError, "not strategy-eligible"):
            MODULE.build(projection, self.nursery)

    def test_held_out_partition_fails_closed(self):
        nursery = copy.deepcopy(self.nursery)
        target = next(
            row["fact_id"]
            for row in self.projection["strategy_queue"]
            if row["capability_demand"] == "type-slice-generalization"
        )
        next(row for row in nursery["entries"] if row["fact_id"] == target)[
            "partition"
        ] = "held-out"
        with self.assertRaisesRegex(ValueError, "not unsealed"):
            MODULE.build(self.projection, nursery)


if __name__ == "__main__":
    unittest.main()
