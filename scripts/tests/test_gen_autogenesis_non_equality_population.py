import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-non-equality-population.py"
SPEC = importlib.util.spec_from_file_location("non_equality_population", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class NonEqualityPopulationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.projection = json.loads(MODULE.PROJECTION.read_text())

    def test_live_population_preserves_positive_and_control_denominators(self):
        result = MODULE.build(self.projection)
        self.assertEqual(result["census"]["positive_targets"], 13)
        self.assertEqual(result["census"]["must_decline_controls"], 6)
        self.assertEqual(len(result["outcomes"]), 19)

    def test_control_cannot_become_strategy_eligible(self):
        projection = copy.deepcopy(self.projection)
        projection["control_observations"][0]["eligible_for_strategy_queue"] = True
        with self.assertRaisesRegex(ValueError, "crossed the strategy boundary"):
            MODULE.build(projection)


if __name__ == "__main__":
    unittest.main()
