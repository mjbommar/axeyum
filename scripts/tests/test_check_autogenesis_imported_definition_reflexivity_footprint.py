import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-imported-definition-reflexivity-footprint.py"
SPEC = importlib.util.spec_from_file_location("definition_footprint", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ImportedDefinitionReflexivityFootprintTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(MODULE.ARTIFACT.read_text())

    def test_live_artifact(self):
        self.assertEqual(
            MODULE.validate(self.data),
            {"controls": 2, "theorem_dependencies": 0, "propext_controls": 2},
        )

    def test_missing_control_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["controls"].pop()
        with self.assertRaisesRegex(ValueError, "population"):
            MODULE.validate(data)

    def test_footprint_omission_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["controls"][0]["axiom_footprint"] = []
        with self.assertRaisesRegex(ValueError, "footprint"):
            MODULE.validate(data)

    def test_theorem_dependency_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["controls"][0]["direct_theorem_dependencies"] = ["Some.theorem"]
        with self.assertRaisesRegex(ValueError, "theorem dependencies"):
            MODULE.validate(data)

    def test_operation_reference_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["controls"][0]["direct_declaration_dependencies"].remove("Nat.testBit")
        with self.assertRaisesRegex(ValueError, "imported operation"):
            MODULE.validate(data)


if __name__ == "__main__":
    unittest.main()
