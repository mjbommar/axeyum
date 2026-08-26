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
                "finite_vectors": 8191,
                "native_analogues": 2,
                "native_boolean_bridges": 1,
                "native_observation_algebras": 1,
                "native_reifications": 1,
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

    def test_imported_footprint_boundary_cannot_gain_unproved_credit(self):
        data = copy.deepcopy(self.data)
        data["imported_definition_footprint_probe"]["status"] = "transport-ready"
        with self.assertRaisesRegex(ValueError, "footprint boundary"):
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

    def test_nat_reification_cannot_gain_unproved_credit(self):
        data = copy.deepcopy(self.data)
        data["native_reification"]["roundtrip_status"] = "proved"
        with self.assertRaisesRegex(ValueError, "reification status changed"):
            MODULE.validate(data)

    def test_reification_step_assumption_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["native_reification"]["step_axiom_footprint_size"] = 1
        with self.assertRaisesRegex(ValueError, "step gained assumptions"):
            MODULE.validate(data)

    def test_boolean_digit_roundtrip_assumption_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["native_reification"]["boolean_digit_roundtrip_axiom_footprint_size"] = 1
        with self.assertRaisesRegex(ValueError, "digit roundtrip gained assumptions"):
            MODULE.validate(data)

    def test_boolean_digit_bound_assumption_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["native_reification"]["boolean_digit_bound_axiom_footprint_size"] = 1
        with self.assertRaisesRegex(ValueError, "digit bound gained assumptions"):
            MODULE.validate(data)

    def test_one_bit_roundtrip_assumption_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["native_reification"]["one_bit_roundtrip_axiom_footprint_size"] = 1
        with self.assertRaisesRegex(ValueError, "one_bit_roundtrip gained assumptions"):
            MODULE.validate(data)

    def test_universal_reification_bound_assumption_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["native_reification"]["reification_bound_axiom_footprint_size"] = 1
        with self.assertRaisesRegex(ValueError, "reification bound gained assumptions"):
            MODULE.validate(data)

    def test_numeric_roundtrip_assumption_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["native_reification"]["numeric_roundtrip_axiom_footprint_size"] = 1
        with self.assertRaisesRegex(ValueError, "numeric reification roundtrip"):
            MODULE.validate(data)

    def test_recursive_roundtrip_assumption_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["native_reification"]["low_reification_roundtrip_axiom_footprint_size"] = 1
        with self.assertRaisesRegex(ValueError, "low_reification_roundtrip"):
            MODULE.validate(data)

    def test_bounded_bitwise_assumption_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["native_reification"]["bounded_bitwise_axiom_footprint_size"] = 1
        with self.assertRaisesRegex(ValueError, "bounded bitwise"):
            MODULE.validate(data)

    def test_outside_reification_assumption_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["native_reification"]["low_reification_outside_axiom_footprint_size"] = 1
        with self.assertRaisesRegex(ValueError, "low_reification_outside"):
            MODULE.validate(data)

    def test_input_bound_assumption_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["native_boolean_bridge"]["input_bound_axiom_footprint_size"] = 1
        with self.assertRaisesRegex(ValueError, "input sufficient-width"):
            MODULE.validate(data)

    def test_total_bitwise_assumption_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["native_reification"]["total_bitwise_axiom_footprint_size"] = 1
        with self.assertRaisesRegex(ValueError, "total bitwise"):
            MODULE.validate(data)

    def test_finite_oracle_receipt_mutation_fails_closed(self):
        data = copy.deepcopy(self.data)
        data["finite_reification_oracle"]["inside_observations"] -= 1
        with self.assertRaisesRegex(ValueError, "oracle receipt"):
            MODULE.validate(data)


if __name__ == "__main__":
    unittest.main()
