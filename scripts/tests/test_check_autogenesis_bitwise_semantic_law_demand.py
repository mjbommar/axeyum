import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-bitwise-semantic-law-demand.py"
SPEC = importlib.util.spec_from_file_location("bitwise_law_demand", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BitwiseSemanticLawDemandTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(MODULE.ARTIFACT.read_text())

    def test_live_artifact(self):
        self.assertEqual(
            MODULE.validate(self.data),
            {
                "laws": 6,
                "native_analogues": 2,
                "native_boolean_bridges": 1,
                "operations": 2,
            },
        )

    def test_missing_law_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["laws"].pop()
        with self.assertRaisesRegex(ValueError, "population"):
            MODULE.validate(data)

    def test_wrong_operation_identity_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["operations"][0]["content_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "implementation graph"):
            MODULE.validate(data)

    def test_operation_footprint_omission_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["operations"][0]["axiom_footprint"] = []
        with self.assertRaisesRegex(ValueError, "operation footprint"):
            MODULE.validate(data)

    def test_countermodel_exclusion_mutation_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["countermodel_exclusion"]["law_rhs"] = False
        with self.assertRaisesRegex(ValueError, "receipt"):
            MODULE.validate(data)

    def test_native_analogue_type_mutation_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["native_analogues"][0]["canonical_type"] += " "
        with self.assertRaisesRegex(ValueError, "type identity"):
            MODULE.validate(data)

    def test_imported_equivalence_cannot_gain_unproved_credit(self):
        data = copy.deepcopy(self.data)
        data["native_boolean_bridge"]["imported_equivalence_status"] = "proved"
        with self.assertRaisesRegex(ValueError, "gained credit"):
            MODULE.validate(data)


if __name__ == "__main__":
    unittest.main()
