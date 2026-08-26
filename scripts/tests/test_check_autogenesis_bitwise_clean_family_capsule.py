import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-bitwise-clean-family-capsule.py"
SPEC = importlib.util.spec_from_file_location("bitwise_family_capsule", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BitwiseCleanFamilyCapsuleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(MODULE.ARTIFACT.read_text())

    def test_live_receipt(self):
        self.assertEqual(
            MODULE.validate(self.data, verify_external=False),
            {"roots": 3, "axioms": 0, "admitted_declarations": 116},
        )

    def test_missing_root_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["roots"].pop()
        with self.assertRaisesRegex(ValueError, "population"):
            MODULE.validate(data, verify_external=False)

    def test_root_assumption_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["roots"][0]["axiom_footprint"] = ["propext"]
        with self.assertRaisesRegex(ValueError, "gained assumptions"):
            MODULE.validate(data, verify_external=False)

    def test_generic_dependency_is_required(self):
        data = copy.deepcopy(self.data)
        data["roots"][0]["direct_theorem_dependencies"] = []
        with self.assertRaisesRegex(ValueError, "bypassed"):
            MODULE.validate(data, verify_external=False)

    def test_external_hash_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["external_stream"]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "digest"):
            MODULE.validate(data, verify_external=True)


if __name__ == "__main__":
    unittest.main()
