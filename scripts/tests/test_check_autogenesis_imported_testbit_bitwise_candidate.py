import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-imported-testbit-bitwise-candidate.py"
SPEC = importlib.util.spec_from_file_location("testbit_candidate", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ImportedTestBitBitwiseCandidateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(MODULE.ARTIFACT.read_text())

    def test_live_receipt_preserves_negative_result(self):
        result = MODULE.validate(self.data, verify_external=False)
        self.assertEqual(result["axiom_footprint"], 5)
        self.assertEqual(result["direct_theorem_dependencies"], 29)

    def test_axiom_free_flip_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["kernel_import"]["axiom_free"] = True
        with self.assertRaisesRegex(ValueError, "must not"):
            MODULE.validate(data, verify_external=False)

    def test_footprint_omission_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["kernel_import"]["axiom_footprint"].remove("propext")
        with self.assertRaisesRegex(ValueError, "footprint"):
            MODULE.validate(data, verify_external=False)

    def test_reconstruction_target_assumption_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["reconstruction_target"]["axiom_footprint"] = ["propext"]
        with self.assertRaisesRegex(ValueError, "reconstruction target"):
            MODULE.validate(data, verify_external=False)


if __name__ == "__main__":
    unittest.main()
