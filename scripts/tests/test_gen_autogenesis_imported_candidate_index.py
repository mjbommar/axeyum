import copy
import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-imported-candidate-index.py"
SPEC = importlib.util.spec_from_file_location("imported_candidate_index", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ImportedCandidateIndexTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.entries = MODULE.audit_entries()

    def test_live_index_routes_bitwise_to_reconstruction(self):
        result = MODULE.build(self.entries)
        self.assertEqual(result["census"], {
            "candidates": 1,
            "candidate_executable": 0,
            "proof_reconstruct_required": 0,
            "clean_definition_reconstruct_required": 1,
        })
        row = result["candidates"][0]
        self.assertEqual(row["name"], "Nat.testBit_bitwise")
        self.assertEqual(
            row["retrieval_disposition"], "clean-definition-reconstruction-required"
        )
        self.assertEqual(row["statement_axiom_floor"], ["propext"])
        self.assertFalse(row["proof_reconstruction_eligible"])
        self.assertFalse(row["execution_eligible"])

    def test_empty_footprint_routes_to_execution(self):
        path, source = self.entries[0]
        data = copy.deepcopy(source)
        data["kernel_import"]["axiom_footprint"] = []
        data["kernel_import"]["axiom_free"] = True
        data.pop("statement_trust_floor")
        result = MODULE.build([(path, data)])
        self.assertEqual(result["census"]["candidate_executable"], 1)
        self.assertEqual(result["candidates"][0]["retrieval_disposition"], "candidate-executable")

    def test_assumption_bearing_candidate_without_floor_routes_to_proof_reconstruction(self):
        path, source = self.entries[0]
        data = copy.deepcopy(source)
        data.pop("statement_trust_floor")
        result = MODULE.build([(path, data)])
        self.assertEqual(result["census"]["proof_reconstruct_required"], 1)
        self.assertEqual(
            result["candidates"][0]["retrieval_disposition"],
            "proof-reconstruct-required",
        )
        self.assertTrue(result["candidates"][0]["proof_reconstruction_eligible"])

    def test_structural_floor_cannot_be_marked_axiom_free(self):
        path, source = self.entries[0]
        data = copy.deepcopy(source)
        data["kernel_import"]["axiom_footprint"] = []
        data["kernel_import"]["axiom_free"] = True
        with self.assertRaisesRegex(ValueError, "axiom-free.*statement trust floor"):
            MODULE.build([(path, data)])

    def test_footprint_flag_mismatch_fails(self):
        path, source = self.entries[0]
        data = copy.deepcopy(source)
        data["kernel_import"]["axiom_free"] = True
        with self.assertRaisesRegex(ValueError, "disagrees"):
            MODULE.build([(path, data)])


if __name__ == "__main__":
    unittest.main()
