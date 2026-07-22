from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_lean_recursive_induction_hypotheses",
    ROOT / "scripts" / "check-lean-recursive-induction-hypotheses.py",
)
assert SPEC and SPEC.loader
CHECK = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECK
SPEC.loader.exec_module(CHECK)


class LeanRecursiveInductionHypothesesM0Tests(unittest.TestCase):
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
            ("sha256", "0" * 64, "stream hash drift"),
            ("bytes", 1, "stream byte count drift"),
            ("records", 1, "stream record count drift"),
            ("selected_root", "Wrong.root", "selected root drift"),
        )
        for key, value, message in mutations:
            with self.subTest(key=key):
                mutated = copy.deepcopy(CHECK.load_manifest())
                mutated["streams"]["vector-computation"][key] = value
                self.data = mutated
                self.assertTrue(any(message in item for item in self.failures()))

    def test_target_inductive_and_recursor_metadata_drift_reject(self) -> None:
        self.data["streams"]["acc-computation"]["inventory"][
            "target_inductive"
        ]["is_reflexive"] = False
        self.assertTrue(
            any("target inductive metadata drift" in item for item in self.failures())
        )

        self.data = CHECK.load_manifest()
        self.data["streams"]["vector-computation"]["inventory"][
            "target_recursor"
        ]["rule_nfields"] = [0, 2]
        self.assertTrue(
            any("target recursor metadata drift" in item for item in self.failures())
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
        self.data["semantic_contract"]["induction_hypothesis"] = "motive (u xs)"
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
        self.data["mandatory_controls"]["strict_positivity_generated_cases"] = 839
        self.assertTrue(
            any("mandatory control contract drift" in item for item in self.failures())
        )

        self.data = CHECK.load_manifest()
        self.data["stop_condition_ids"].pop()
        self.assertTrue(
            any("stop-condition population" in item for item in self.failures())
        )

    def test_baseline_fixture_hash_drift_rejects(self) -> None:
        self.data["baseline"]["direct_recursive_control"]["sha256"] = "f" * 64
        failures = self.failures()
        self.assertTrue(any("baseline identity/outcome" in item for item in failures))
        self.assertTrue(any("baseline fixture hash drift" in item for item in failures))

        self.data = CHECK.load_manifest()
        self.data["baseline"]["recursive_indexed"]["registered_outcome"] = "accepted"
        self.assertTrue(
            any("baseline identity/outcome" in item for item in self.failures())
        )

    def test_premature_axeyum_observation_rejects(self) -> None:
        self.data["kernel_results"] = {"vector-computation": "accepted"}
        failures = self.failures()
        self.assertTrue(any("top-level fields drift" in item for item in failures))
        self.assertTrue(any("premature Axeyum observations" in item for item in failures))


if __name__ == "__main__":
    unittest.main()
