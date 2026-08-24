import copy
import importlib.util
import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "capability_candidate_demand",
    ROOT / "scripts/validate-autogenesis-capability-candidate-demand.py",
)
assert SPEC and SPEC.loader
DEMAND = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(DEMAND)


class CapabilityCandidateDemandControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(
            (ROOT / "artifacts/autogenesis/capability-candidate-demand-v1.json").read_text()
        )

    def test_current_projection_is_valid(self):
        self.assertEqual(DEMAND.validate(self.data), [])

    def test_invented_obstruction_is_rejected(self):
        data = copy.deepcopy(self.data)
        data["candidates"][0]["obstruction_ids"].append("O:invented")
        self.assertTrue(any("obstruction identifiers" in error for error in DEMAND.validate(data)))

    def test_invented_candidate_status_is_rejected(self):
        data = copy.deepcopy(self.data)
        data["candidates"][0]["overlay_status"] = "active"
        self.assertTrue(any("not candidate" in error for error in DEMAND.validate(data)))
