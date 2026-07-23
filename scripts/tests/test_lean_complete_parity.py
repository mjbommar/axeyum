from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "gen_lean_complete_parity",
    ROOT / "scripts" / "gen-lean-complete-parity.py",
)
assert SPEC and SPEC.loader
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class LeanCompleteParityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = GEN.load_manifest()

    def population(self, population_id: str) -> dict:
        return next(item for item in self.data["populations"] if item["id"] == population_id)

    def axis(self, axis_id: str) -> dict:
        return next(item for item in self.data["axes"] if item["id"] == axis_id)

    def gate(self, gate_id: str) -> dict:
        return next(item for item in self.data["terminal_gates"] if item["id"] == gate_id)

    def failures(self) -> list[str]:
        return GEN.validate_manifest(self.data)

    def test_committed_registry_is_valid_and_rendering_is_deterministic(self) -> None:
        self.assertEqual(self.failures(), [])
        first = GEN.build_report(self.data)
        second = GEN.build_report(copy.deepcopy(self.data))
        self.assertEqual(first, second)
        markdown = GEN.render_markdown(first)
        self.assertIn("complete Lean 4.30 parity not established", markdown)
        self.assertIn("Registered terminal cells: **0**", markdown)
        self.assertFalse(first["terminal"]["ready"])
        self.assertEqual(first["bounded_snapshot"]["axiom_ledger"]["rows"], 65)
        self.assertEqual(
            first["bounded_snapshot"]["construct_matrix"]["independently_admitted"],
            6,
        )
        u2 = first["bounded_snapshot"]["u2_test_authority"]
        self.assertEqual(
            [(item["id"], item["registered"]) for item in u2["profiles"]],
            [("default", 3678), ("full-lake", 3723)],
        )
        official = first["bounded_snapshot"]["u2_official_execution_authority"]
        self.assertEqual(official["process_attempts"], 4)
        self.assertEqual(official["incomplete_process_attempts"], 2)
        self.assertEqual(official["official_outcomes"], 2)
        self.assertEqual(official["official_passes"], 1)
        self.assertEqual(official["official_failures"], 1)
        self.assertEqual(official["axeyum_outcomes"], 0)
        self.assertEqual(official["paired_cells"], 0)
        self.assertEqual(official["credits"]["parity_credit"], 0)
        m2 = first["bounded_snapshot"]["u2_m2_execution_contract"]
        self.assertEqual(m2["case_count"], 64)
        self.assertEqual(m2["first_case_id"], "compile/uint_fold.lean")
        self.assertEqual(m2["last_case_id"], "docparse/block_0004.txt")
        self.assertFalse(m2["live_execution_surface"])
        self.assertEqual(m2["official_outcomes"], 0)
        self.assertEqual(m2["parity_credit"], 0)
        self.assertEqual(m2["store"]["fixed_json"], 15)
        self.assertEqual(m2["store"]["fixed_raw"], 4)
        self.assertEqual(m2["store"]["case_records"], 64)
        self.assertTrue(m2["runner"]["run_command_exposed"])
        self.assertFalse(m2["runner"]["live_execution_observed"])
        self.assertEqual(u2["outcomes"]["paired_registered"], 0)
        u2_ci = first["bounded_snapshot"]["u2_ci_profile_authority"]
        self.assertEqual(u2_ci["derivation"]["contexts"], 17)
        self.assertEqual(u2_ci["derivation"]["candidate_cells"], 153)
        self.assertEqual(u2_ci["derivation"]["ctest_attempts"], 111)
        self.assertEqual(u2_ci["derivation"]["selection_sets"], 8)
        self.assertEqual(u2_ci["outcomes"]["official_executed_attempts"], 0)
        u2_shards = first["bounded_snapshot"]["u2_child_shard_authority"]
        self.assertEqual(u2_shards["status"], "complete-derivation-not-run")
        self.assertEqual(u2_shards["summary"]["distinct_membership_plans"], 5)
        self.assertEqual(u2_shards["summary"]["physical_child_shards"], 289)
        self.assertEqual(
            u2_shards["summary"]["selection_expanded_shard_occurrences"], 461
        )
        self.assertEqual(
            u2_shards["summary"]["attempt_expanded_shard_occurrences"], 6451
        )
        self.assertTrue(u2_shards["claims"]["parent_memberships_partitioned"])
        self.assertFalse(u2_shards["claims"]["official_execution_complete"])
        self.assertTrue(all(value == 0 for value in u2_shards["credits"].values()))
        execution = first["bounded_snapshot"]["execution_evidence_authority"]
        self.assertEqual(execution["lane_policies"], 2)
        self.assertEqual(execution["termination_classes"], 12)
        self.assertEqual(execution["synthetic_controls"], 5)
        self.assertEqual(execution["mutation_classes"], 19)
        self.assertTrue(execution["all_synthetic_controls_valid"])
        self.assertEqual(execution["observed"]["real_runs"], 0)
        process = first["bounded_snapshot"]["execution_process_authority"]
        self.assertEqual(process["registered_controls"], 8)
        self.assertEqual(process["retained_process_attempts"], 8)
        self.assertEqual(process["classification_counts"], {
            "exited": 2,
            "signaled": 1,
            "wall-timeout": 1,
            "memory-limit": 2,
            "launch-failed": 1,
            "preflight-invalid": 1,
        })
        self.assertEqual(process["retained_files"], 40)
        self.assertEqual(process["raw_artifacts"], 16)
        self.assertEqual(process["case_records"], 0)
        self.assertEqual(process["completion_records"], 0)
        self.assertTrue(all(value == 0 for value in process["credits"].values()))
        store = first["bounded_snapshot"]["execution_store_authority"]
        self.assertEqual(store["storage_classes"], 2)
        self.assertEqual(store["kill_cells"], 16)
        self.assertEqual(store["sigkill_cells"], 16)
        self.assertEqual(store["projection_equal_cells"], 16)
        self.assertEqual(store["evidence_files"], 65)
        self.assertEqual(store["real_outcomes"], 0)
        self.assertEqual(store["completed_u2_cases"], 0)
        self.assertEqual(store["paired_cells"], 0)
        self.assertEqual(store["performance_rows"], 0)
        self.assertEqual(store["parity_credit"], 0)
        self.assertTrue(store["claims"]["process_sigkill_recovery"])
        self.assertFalse(store["claims"]["power_loss_recovery"])
        acceptance = first["bounded_snapshot"]["execution_acceptance_authority"]
        self.assertEqual(acceptance["status"], "accepted-no-credit-real-controls")
        self.assertEqual(acceptance["observed_external_process_attempts"], 3)
        self.assertEqual(acceptance["failed_external_process_attempts"], 1)
        self.assertEqual(acceptance["completed_external_controls"], 2)
        self.assertEqual(acceptance["retained_files"], 67)
        self.assertEqual(acceptance["retained_bytes"], 142523)
        self.assertEqual(acceptance["u2_cases"], 0)
        self.assertEqual(acceptance["official_outcomes"], 0)
        self.assertEqual(acceptance["axeyum_outcomes"], 0)
        self.assertEqual(acceptance["paired_cells"], 0)
        self.assertEqual(acceptance["performance_rows"], 0)
        self.assertTrue(acceptance["claims"]["real_process_controls"])
        self.assertFalse(acceptance["claims"]["official_u2_execution"])
        self.assertTrue(all(value == 0 for value in acceptance["credits"].values()))
        source_paths = {item["path"] for item in first["source_identities"]}
        self.assertIn(".github/workflows/ci.yml", source_paths)
        self.assertIn(
            "docs/plan/lean4-complete-parity-contract-2026-07-22.md", source_paths
        )
        self.assertIn("scripts/gen-lean-complete-parity.py", source_paths)
        self.assertIn("docs/plan/lean-u2-test-authority-v1.json", source_paths)
        self.assertIn("docs/plan/lean-u2-official-ci-profiles-v1.json", source_paths)
        self.assertIn("docs/plan/lean-u2-official-child-shards-v1.json", source_paths)
        self.assertIn("scripts/gen-lean-u2-official-child-shards.py", source_paths)
        self.assertIn("docs/plan/lean-execution-evidence-v1.json", source_paths)
        self.assertIn("docs/plan/lean-execution-process-v1.json", source_paths)
        self.assertIn("docs/plan/lean-execution-store-v1.json", source_paths)
        self.assertIn("docs/plan/lean-execution-acceptance-v1.json", source_paths)
        self.assertIn("scripts/lean_execution_acceptance.py", source_paths)
        self.assertIn(
            "docs/plan/lean-u2-official-execution-tl0.6.3-m0-r3-v1.json",
            source_paths,
        )
        self.assertIn("scripts/lean_u2_official_execution.py", source_paths)
        self.assertIn("scripts/lean_u2_official_execution_r3_result.py", source_paths)
        self.assertIn("scripts/lean_u2_official_execution_m2.py", source_paths)
        self.assertIn(
            "scripts/tests/test_lean_u2_official_execution_m2.py", source_paths
        )
        self.assertIn("scripts/lean_u2_official_execution_m2_store.py", source_paths)
        self.assertIn(
            "scripts/tests/test_lean_u2_official_execution_m2_store.py",
            source_paths,
        )
        self.assertIn("scripts/lean_u2_official_execution_m2_run.py", source_paths)
        self.assertIn(
            "scripts/tests/test_lean_u2_official_execution_m2_run.py",
            source_paths,
        )
        self.assertIn(
            "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r1-result-v1.json",
            source_paths,
        )
        self.assertIn(
            "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r1-result-2026-07-22.md",
            source_paths,
        )

    def test_u2_registration_is_bounded_not_terminal_authority(self) -> None:
        population = self.population("U2")
        self.assertEqual(population["state"], "bounded_profile")
        self.assertIsNone(population["raw_denominator"])
        self.assertIsNone(population["normalized_denominator"])
        self.assertIsNone(population["content_digest"])
        self.assertIn(
            "all 111 official attempts remain incomplete",
            population["residual"],
        )
        self.assertIn(
            "Completion-last policy therefore grants zero M2 case or shard credit",
            population["residual"],
        )

    def test_population_order_and_incomplete_denominators_are_fail_closed(self) -> None:
        self.data["populations"][0], self.data["populations"][1] = (
            self.data["populations"][1],
            self.data["populations"][0],
        )
        self.assertTrue(any("population ids/order" in failure for failure in self.failures()))

        self.data = GEN.load_manifest()
        self.population("U1")["raw_denominator"] = 12
        self.assertTrue(
            any("cannot publish terminal denominators" in failure for failure in self.failures())
        )

    def test_complete_population_requires_both_denominators_and_digest(self) -> None:
        population = self.population("U1")
        population["state"] = "complete_authority"
        self.assertTrue(
            any("needs raw denominator" in failure for failure in self.failures())
        )
        self.assertTrue(
            any("needs normalized denominator" in failure for failure in self.failures())
        )
        self.assertTrue(any("needs content digest" in failure for failure in self.failures()))

    def test_axis_credit_requires_evidence_and_complete_dependencies(self) -> None:
        self.axis("A3")["state"] = "partial"
        self.assertTrue(
            any(
                "A3: retained evidence is required" in failure
                for failure in self.failures()
            )
        )

        self.data = GEN.load_manifest()
        self.axis("A1")["populations"] = ["U1"]
        self.assertTrue(
            any("population dependencies must match" in failure for failure in self.failures())
        )

        self.data = GEN.load_manifest()
        self.axis("A1")["state"] = "complete"
        self.assertTrue(
            any(
                "complete axis depends on incomplete populations" in failure
                for failure in self.failures()
            )
        )

    def test_derived_gates_and_claim_switch_cannot_be_hand_promoted(self) -> None:
        self.gate("G1")["state"] = "satisfied"
        self.assertTrue(
            any(
                "G1: state disagrees with derived registry evidence" in failure
                for failure in self.failures()
            )
        )

        self.data = GEN.load_manifest()
        self.data["terminal_claim_enabled"] = True
        self.assertTrue(
            any(
                "terminal_claim_enabled must exactly equal" in failure
                for failure in self.failures()
            )
        )

        self.data = GEN.load_manifest()
        self.gate("G4")["state"] = "satisfied"
        self.assertTrue(
            any(
                "G4: retained evidence is required" in failure
                for failure in self.failures()
            )
        )

    def test_paired_taxonomy_and_cells_require_exact_identity(self) -> None:
        self.assertIn("command_sha256", GEN.PAIRED_CELL_FIELDS)
        self.assertIn("environment_sha256", GEN.PAIRED_CELL_FIELDS)
        self.assertIn("resource_envelope_sha256", GEN.PAIRED_CELL_FIELDS)
        self.assertIn("attempt_id", GEN.PAIRED_CELL_FIELDS)
        self.assertIn("completed", GEN.PAIRED_CELL_FIELDS)
        self.data["outcome_classes"][-1] = "other"
        self.assertTrue(any("outcome_classes/order" in failure for failure in self.failures()))

        self.data = GEN.load_manifest()
        self.data["paired_cells"] = [
            {
                "id": "bounded-probe",
                "population": "U1",
                "axis": "A1",
                "outcome": "agree-success",
                "source_sha256": "bad",
                "dependency_sha256": "bad",
                "source_family": "probe",
                "normalization": "kernel expression normalization v1",
                "official_evidence": [],
                "axeyum_evidence": [],
            }
        ]
        failures = self.failures()
        self.assertTrue(any("source_sha256 must be" in failure for failure in failures))
        self.assertTrue(any("dependency_sha256 must be" in failure for failure in failures))
        self.assertTrue(
            any(
                "official_evidence: retained evidence" in failure
                for failure in failures
            )
        )
        self.assertTrue(any("G3: state disagrees" in failure for failure in failures))

    def test_claim_detector_rejects_affirmative_claims_only(self) -> None:
        self.assertEqual(
            GEN.find_forbidden_claims("Axeyum has complete Lean 4.30 parity."),
            [(1, "Axeyum has complete Lean 4.30 parity")],
        )
        self.assertTrue(GEN.find_forbidden_claims("We have reached 100% Lean 4 parity."))
        self.assertTrue(
            GEN.find_forbidden_claims("Axeyum has **full** Lean 4 compatibility.")
        )
        self.assertTrue(GEN.find_forbidden_claims("Lean 4 parity is complete."))
        self.assertEqual(
            GEN.find_forbidden_claims("Axeyum does not have complete Lean 4 parity."),
            [],
        )
        self.assertEqual(
            GEN.find_forbidden_claims("Complete Lean 4 parity is a long-term target."),
            [],
        )

    def test_missing_evidence_path_is_rejected(self) -> None:
        self.population("U1")["evidence"][0]["path"] = "docs/plan/does-not-exist.json"
        self.assertTrue(any("missing evidence path" in failure for failure in self.failures()))


if __name__ == "__main__":
    unittest.main()
