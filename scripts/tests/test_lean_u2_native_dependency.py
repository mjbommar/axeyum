from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "gen_lean_u2_native_dependency",
    ROOT / "scripts/gen-lean-u2-native-dependency.py",
)
assert SPEC and SPEC.loader
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class LeanU2NativeDependencyContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.data = GEN.build_authority()

    def test_registry_contract_is_exact_and_sealed(self) -> None:
        self.assertEqual(
            [row["id"] for row in self.data["node_types"]],
            [row["id"] for row in GEN.NODE_TYPES],
        )
        self.assertEqual(
            [row["id"] for row in self.data["edge_types"]],
            [row["id"] for row in GEN.EDGE_TYPES],
        )
        self.assertEqual(
            [row["id"] for row in self.data["evidence_states"]],
            [row["id"] for row in GEN.EVIDENCE_STATES],
        )
        self.assertEqual(len(self.data["node_types"]), 11)
        self.assertEqual(len(self.data["edge_types"]), 31)
        self.assertEqual(len(self.data["evidence_states"]), 9)
        self.assertEqual(len(self.data["resolvers"]), 7)
        for field in ("node_types", "edge_types", "evidence_states", "resolvers"):
            self.assertTrue(all(len(row["record_sha256"]) == 64 for row in self.data[field]))

    def test_parent_projection_and_variant_factoring_are_complete(self) -> None:
        summary = self.data["summary"]
        self.assertEqual(summary["registration_cases"], 3723)
        self.assertEqual(summary["selection_sets"], 8)
        self.assertEqual(summary["provider_variants"], 111)
        self.assertEqual(summary["case_variant_occurrences"], 408374)
        self.assertEqual(
            sum(row["provider_variant_count"] for row in self.data["case_rows"]),
            summary["case_variant_occurrences"],
        )
        selection_ids = {row["selection_set_id"] for row in self.data["selection_rows"]}
        self.assertEqual(len(selection_ids), 8)
        self.assertTrue(
            all(
                set(row["applicable_selection_set_ids"]).issubset(selection_ids)
                for row in self.data["case_rows"]
            )
        )

    def test_empty_graph_and_zero_credit_boundary_are_explicit(self) -> None:
        self.assertEqual(self.data["nodes"], [])
        self.assertEqual(self.data["edges"], [])
        self.assertEqual(self.data["summary"]["resolved_case_closures"], 0)
        self.assertEqual(self.data["summary"]["external_processes"], 0)
        self.assertEqual(self.data["summary"]["native_outcomes"], 0)
        self.assertEqual(self.data["summary"]["paired_cells"], 0)
        self.assertTrue(all(value == 0 for value in self.data["credits"].values()))
        self.assertFalse(self.data["claims"]["provider_identity_bound"])
        self.assertFalse(self.data["claims"]["tl0_6_4_complete"])
        self.assertFalse(self.data["claims"]["lean_parity_established"])

    def test_every_variant_and_case_starts_unresolved_and_not_run(self) -> None:
        self.assertTrue(
            all(
                row["provider_state"] == "unbound"
                and row["dependency_state"] == "not-run"
                and row["attempt_state"] == "not-run"
                and row["provider_identity"] is None
                and row["platform_identity"] is None
                and row["configuration_identity"] is None
                and row["resource_lane"] is None
                for row in self.data["provider_variants"]
            )
        )
        self.assertTrue(
            all(
                row["dependency_state"] == "not-run"
                and row["node_count"] == 0
                and row["edge_count"] == 0
                and row["native_outcome"] == "not-run"
                and row["execution_credit"] == 0
                and row["pairing_credit"] == 0
                for row in self.data["case_rows"]
            )
        )


@unittest.skipUnless(GEN.MANIFEST.is_file(), "M2.0 authority not derived yet")
class LeanU2NativeDependencyAuthorityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = GEN.load_json(GEN.MANIFEST)

    def failures(self) -> list[str]:
        return GEN.validate_authority(self.data)

    def reseal_top(self) -> None:
        self.data["record_sha256"] = GEN.domain_digest(
            GEN.SCHEMA,
            {key: value for key, value in self.data.items() if key != "record_sha256"},
        )

    def reseal_row(self, field: str, index: int, domain: str) -> None:
        row = self.data[field][index]
        self.data[field][index] = GEN.seal(row, domain)

    def reseal_list(self, field: str, domain: str) -> None:
        self.data[f"{field}_sha256"] = GEN.domain_digest(domain, self.data[field])
        self.reseal_top()

    def test_committed_authority_is_valid_deterministic_and_non_crediting(self) -> None:
        self.assertEqual(self.failures(), [])
        first = GEN.summarize(self.data)
        second = GEN.summarize(GEN.load_json(GEN.MANIFEST))
        self.assertEqual(first, second)
        self.assertIn("all dependency resolution", first["verdict"])
        self.assertTrue(all(value == 0 for value in first["credits"].values()))

    def test_registry_mutation_is_rejected_after_resealing(self) -> None:
        self.data["edge_types"][0]["requires_observation"] = True
        self.reseal_row("edge_types", 0, GEN.EDGE_DOMAIN)
        self.reseal_list(
            "edge_types", "axeyum-lean-u2-native-dependency-edge-types-v1"
        )
        self.assertTrue(any("edge_types semantic" in item for item in self.failures()))

    def test_selection_mutation_is_rejected_after_resealing(self) -> None:
        self.data["selection_rows"][0]["selected_count"] -= 1
        self.reseal_row("selection_rows", 0, GEN.SELECTION_DOMAIN)
        self.reseal_list(
            "selection_rows", "axeyum-lean-u2-native-dependency-selections-v1"
        )
        self.assertTrue(
            any("selection_rows semantic" in item for item in self.failures())
        )

    def test_provider_binding_and_execution_claim_are_rejected_after_resealing(self) -> None:
        row = self.data["provider_variants"][0]
        row["provider_state"] = "bound"
        row["attempt_state"] = "passed"
        row["provider_identity"] = {"invented": True}
        self.reseal_row("provider_variants", 0, GEN.VARIANT_DOMAIN)
        self.reseal_list(
            "provider_variants",
            "axeyum-lean-u2-native-dependency-provider-variants-v1",
        )
        self.assertTrue(
            any("provider_variants semantic" in item for item in self.failures())
        )

    def test_case_closure_and_credit_mutation_are_rejected_after_resealing(self) -> None:
        row = self.data["case_rows"][0]
        row["dependency_state"] = "complete"
        row["unresolved"] = []
        row["native_outcome"] = "passed"
        row["execution_credit"] = 1
        self.reseal_row("case_rows", 0, GEN.CASE_DOMAIN)
        self.reseal_list("case_rows", "axeyum-lean-u2-native-dependency-cases-v1")
        self.assertTrue(any("case_rows semantic" in item for item in self.failures()))

    def test_nonempty_node_and_edge_lists_are_rejected_after_resealing(self) -> None:
        self.data["nodes"] = [{"id": "invented"}]
        self.data["edges"] = [{"id": "invented"}]
        self.data["nodes_sha256"] = GEN.domain_digest(
            "axeyum-lean-u2-native-dependency-nodes-v1", self.data["nodes"]
        )
        self.data["edges_sha256"] = GEN.domain_digest(
            "axeyum-lean-u2-native-dependency-edges-v1", self.data["edges"]
        )
        self.reseal_top()
        failures = self.failures()
        self.assertIn("M2.0 nodes must be empty", failures)
        self.assertIn("M2.0 edges must be empty", failures)

    def test_parent_claim_and_credit_mutations_are_rejected_after_resealing(self) -> None:
        self.data["parent_logical_seals"]["m1_case_rows_sha256"] = "0" * 64
        self.data["claims"]["lean_parity_established"] = True
        self.data["credits"]["parity_credit"] = 1
        self.reseal_top()
        failures = self.failures()
        self.assertIn("parent_logical_seals drift", failures)
        self.assertIn("claims drift", failures)
        self.assertIn("credits drift", failures)

    def test_list_summary_and_top_level_seals_have_teeth(self) -> None:
        self.data["case_rows_sha256"] = "0" * 64
        self.data["summary"]["registration_cases"] = 3722
        self.data["record_sha256"] = "1" * 64
        failures = self.failures()
        self.assertIn("case_rows list seal drift", failures)
        self.assertIn("summary drift", failures)
        self.assertIn("top-level record seal drift", failures)


if __name__ == "__main__":
    unittest.main()
