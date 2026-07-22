from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_lean_nested_inductive_elimination",
    ROOT / "scripts" / "check-lean-nested-inductive-elimination.py",
)
assert SPEC and SPEC.loader
CHECK = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECK
SPEC.loader.exec_module(CHECK)


class LeanNestedInductiveEliminationM0Tests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = CHECK.load_manifest()

    def failures(self) -> list[str]:
        return CHECK.validate_manifest(self.data)

    def test_committed_source_wire_freeze_is_valid(self) -> None:
        self.assertEqual(self.failures(), [])

    def test_positive_source_hash_and_root_drift_reject(self) -> None:
        self.data["positive_source"]["sha256"] = "0" * 64
        self.assertTrue(any("positive source" in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["positive_source"]["roots"][0]["expected_normal_form"] = (
            "MiniNat.zero"
        )
        self.assertTrue(
            any("roots or normal forms drift" in item for item in self.failures())
        )

    def test_negative_source_diagnostic_and_status_drift_reject(self) -> None:
        self.data["negative_source"]["diagnostic"] = "wrong diagnostic"
        self.assertTrue(any("negative source" in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["negative_source"]["compile_exit_statuses"] = [0, 0]
        self.assertTrue(any("negative source" in item for item in self.failures()))

    def test_stream_hash_size_record_and_root_drift_reject(self) -> None:
        mutations = (
            ("sha256", "f" * 64, "stream sha256 drift"),
            ("bytes", 1, "stream bytes drift"),
            ("records", 1, "stream records drift"),
            ("selected_root", "Wrong.root", "stream selected_root drift"),
        )
        for key, value, message in mutations:
            with self.subTest(key=key):
                mutated = copy.deepcopy(CHECK.load_manifest())
                mutated["streams"]["auxiliary-recursion-computation"][key] = value
                self.data = mutated
                self.assertTrue(any(message in item for item in self.failures()))

    def test_num_nested_and_family_metadata_drift_reject(self) -> None:
        inventory = self.data["streams"]["indexed-container-computation"][
            "inventory"
        ]
        inventory["families"][0]["num_nested"] = 0
        self.assertTrue(
            any("registered family metadata drift" in item for item in self.failures())
        )

    def test_wire_recursor_order_and_index_metadata_drift_reject(self) -> None:
        inventory = self.data["streams"]["repeated-container-reuse-computation"][
            "inventory"
        ]
        inventory["wire_recursor_order"].reverse()
        self.assertTrue(
            any(
                "registered wire recursor order drift" in item
                for item in self.failures()
            )
        )

        self.data = CHECK.load_manifest()
        inventory = self.data["streams"]["indexed-container-computation"][
            "inventory"
        ]
        inventory["recursors"][0]["num_indices"] = 0
        self.assertTrue(
            any(
                "registered recursor metadata drift" in item
                for item in self.failures()
            )
        )

    def test_pin_resource_and_command_drift_reject(self) -> None:
        self.data["pins"]["lean"]["version"] = "4.29.0"
        self.assertTrue(any("tool pin drift" in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["resource_policy"]["memory_max"] = "8G"
        self.assertTrue(
            any("resource policy drift" in item for item in self.failures())
        )

        self.data = CHECK.load_manifest()
        self.data["commands"]["positive_compile_argv"][3] = "-j8"
        self.assertTrue(
            any("positive Lean compile argv drift" in item for item in self.failures())
        )

    def test_semantic_contract_and_claim_limit_drift_reject(self) -> None:
        self.data["semantic_contract"]["deduplication"] = "definitional equality"
        self.assertTrue(
            any("semantic contract drift" in item for item in self.failures())
        )

        self.data = CHECK.load_manifest()
        self.data["claim_limits"]["axeyum_import_new_streams"] = "passed"
        self.assertTrue(any("premature product credit" in item for item in self.failures()))

    def test_case_and_mutation_population_order_identity_are_frozen(self) -> None:
        self.data["case_ids"].pop()
        self.assertTrue(any("case population" in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["case_ids"][1] = self.data["case_ids"][0]
        failures = self.failures()
        self.assertTrue(any("case population" in item for item in failures))
        self.assertTrue(any("case IDs must be unique" in item for item in failures))

        self.data = CHECK.load_manifest()
        self.data["mutation_ids"][0], self.data["mutation_ids"][1] = (
            self.data["mutation_ids"][1],
            self.data["mutation_ids"][0],
        )
        self.assertTrue(any("mutation population" in item for item in self.failures()))

    def test_generated_control_and_stop_condition_drift_reject(self) -> None:
        self.data["generated_grammar"]["minimum_unique_cases"] = 320
        self.assertTrue(
            any("generated grammar contract drift" in item for item in self.failures())
        )

        self.data = CHECK.load_manifest()
        self.data["mandatory_controls"]["mutual_generated_cases"] = 719
        self.assertTrue(
            any("mandatory control contract drift" in item for item in self.failures())
        )

        self.data = CHECK.load_manifest()
        self.data["stop_condition_ids"].pop()
        self.assertTrue(
            any("stop-condition population" in item for item in self.failures())
        )

    def test_baseline_hash_and_outcome_drift_reject(self) -> None:
        self.data["baseline"]["nested_stream"]["sha256"] = "0" * 64
        failures = self.failures()
        self.assertTrue(any("baseline identity/outcome" in item for item in failures))
        self.assertTrue(any("baseline artifact hash drift" in item for item in failures))

        self.data = CHECK.load_manifest()
        self.data["baseline"]["nested_stream"]["registered_outcome"] = (
            "CompletedImport"
        )
        self.assertTrue(
            any("baseline identity/outcome" in item for item in self.failures())
        )

    def test_future_assurance_overlay_preserves_m0_baseline_binding(self) -> None:
        row = self.data["baseline"]["construct_matrix"]
        digest = CHECK.construct_matrix_baseline_sha256(CHECK.ROOT / row["path"])
        self.assertEqual(digest, row["sha256_without_tl2_14_overlay"])

    def test_premature_axeyum_observation_rejects(self) -> None:
        self.data["kernel_results"] = {
            "auxiliary-recursion-computation": "accepted"
        }
        failures = self.failures()
        self.assertTrue(any("top-level fields drift" in item for item in failures))
        self.assertTrue(any("premature product observation" in item for item in failures))


if __name__ == "__main__":
    unittest.main()
