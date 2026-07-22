from __future__ import annotations

import copy
import importlib.util
import json
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_lean_mutual_inductive_groups",
    ROOT / "scripts" / "check-lean-mutual-inductive-groups.py",
)
assert SPEC and SPEC.loader
CHECK = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECK
SPEC.loader.exec_module(CHECK)


class LeanMutualInductiveGroupsM0Tests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = CHECK.load_manifest()

    def failures(self) -> list[str]:
        return CHECK.validate_manifest(self.data)

    def test_committed_source_wire_freeze_is_valid(self) -> None:
        self.assertEqual(self.failures(), [])

    def test_source_hash_and_root_drift_reject(self) -> None:
        self.data["source"]["sha256"] = "0" * 64
        self.assertTrue(
            any("computation source hash drift" in item for item in self.failures())
        )

        self.data = CHECK.load_manifest()
        self.data["source"]["roots"][0]["expected_normal_form"] = "MiniNat.zero"
        self.assertTrue(
            any("roots or normal forms drift" in item for item in self.failures())
        )

    def test_stream_hash_size_and_selected_root_drift_reject(self) -> None:
        mutations = (
            ("sha256", "0" * 64, "stream sha256 drift"),
            ("bytes", 1, "stream bytes drift"),
            ("records", 1, "stream records drift"),
            ("selected_root", "Wrong.root", "stream selected_root drift"),
        )
        for key, value, message in mutations:
            with self.subTest(key=key):
                mutated = copy.deepcopy(CHECK.load_manifest())
                mutated["streams"]["cross-family-computation"][key] = value
                self.data = mutated
                self.assertTrue(any(message in item for item in self.failures()))

    def test_family_order_and_metadata_drift_reject(self) -> None:
        inventory = self.data["streams"]["cross-family-computation"]["inventory"]
        inventory["family_order"].reverse()
        self.assertTrue(any("family order drift" in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        inventory = self.data["streams"]["indexed-cross-family-computation"][
            "inventory"
        ]
        inventory["families"][1]["num_indices"] = 0
        self.assertTrue(
            any("registered family metadata drift" in item for item in self.failures())
        )

    def test_wire_recursor_order_and_metadata_drift_reject(self) -> None:
        inventory = self.data["streams"]["cross-family-computation"]["inventory"]
        inventory["wire_recursor_order"].reverse()
        self.assertTrue(
            any("registered wire recursor order drift" in item for item in self.failures())
        )

        self.data = CHECK.load_manifest()
        inventory = self.data["streams"]["indexed-cross-family-computation"][
            "inventory"
        ]
        inventory["recursors"][0]["num_motives"] = 1
        self.assertTrue(
            any("registered recursor metadata drift" in item for item in self.failures())
        )

    def test_pin_resource_and_command_drift_reject(self) -> None:
        mutations = (
            ("pins", "lean", "version", "4.29.0", "tool pin drift"),
            (
                "resource_policy",
                None,
                "memory_max",
                "8G",
                "resource policy drift",
            ),
        )
        for section, subsection, key, value, message in mutations:
            with self.subTest(section=section, key=key):
                mutated = copy.deepcopy(CHECK.load_manifest())
                target = mutated[section]
                if subsection is not None:
                    target = target[subsection]
                target[key] = value
                self.data = mutated
                self.assertTrue(any(message in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["commands"]["lean_compile_argv"][3] = "-j8"
        self.assertTrue(any("Lean compile argv drift" in item for item in self.failures()))

    def test_semantic_contract_and_claim_limit_drift_reject(self) -> None:
        self.data["semantic_contract"]["wire_recursor_order"] = "family order"
        self.assertTrue(any("semantic contract drift" in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["claim_limits"]["axeyum_import"] = "passed"
        self.assertTrue(
            any("claim limits drift" in item for item in self.failures())
        )

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
        self.data["generated_grammar"]["minimum_unique_cases"] = 256
        self.assertTrue(
            any("generated grammar contract drift" in item for item in self.failures())
        )

        self.data = CHECK.load_manifest()
        self.data["mandatory_controls"]["recursive_generated_cases"] = 767
        self.assertTrue(
            any("mandatory control contract drift" in item for item in self.failures())
        )

        self.data = CHECK.load_manifest()
        self.data["stop_condition_ids"].pop()
        self.assertTrue(
            any("stop-condition population" in item for item in self.failures())
        )

    def test_baseline_fixture_and_outcome_drift_reject(self) -> None:
        self.data["baseline"]["mutual_stream"]["sha256"] = "f" * 64
        failures = self.failures()
        self.assertTrue(any("baseline identity/outcome" in item for item in failures))
        self.assertTrue(any("baseline artifact hash drift" in item for item in failures))

        self.data = CHECK.load_manifest()
        self.data["baseline"]["mutual_stream"]["registered_outcome"] = (
            "completed-import"
        )
        self.assertTrue(
            any("baseline identity/outcome" in item for item in self.failures())
        )

    def test_later_assurance_overlays_preserve_m0_baseline_binding(self) -> None:
        row = self.data["baseline"]["construct_matrix"]
        path = CHECK.ROOT / row["path"]
        digest = CHECK.baseline_artifact_sha256(path, "construct_matrix")
        self.assertEqual(digest, row["sha256"])
        current = json.loads(path.read_text(encoding="utf-8"))
        self.assertIn("tl2_13_update", current)
        self.assertIn("tl2_14_update", current)

    def test_premature_axeyum_observation_rejects(self) -> None:
        self.data["kernel_results"] = {"cross-family-computation": "accepted"}
        failures = self.failures()
        self.assertTrue(any("top-level fields drift" in item for item in failures))
        self.assertTrue(any("premature product observation" in item for item in failures))


if __name__ == "__main__":
    unittest.main()
