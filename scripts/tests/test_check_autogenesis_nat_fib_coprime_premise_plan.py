from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import pathlib
import tempfile
import unittest
from contextlib import contextmanager


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-nat-fib-coprime-premise-plan.py"
SPEC = importlib.util.spec_from_file_location("check_fib_coprime_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


@contextmanager
def pinned_observation(manifest: dict, observation: dict):
    temporary = tempfile.TemporaryDirectory()
    directory = pathlib.Path(temporary.name)
    path = directory / "observation.json"
    path.write_text(json.dumps(observation, sort_keys=True) + "\n")
    path.chmod(0o444)
    directory.chmod(0o555)
    changed = copy.deepcopy(manifest)
    changed["composition_probe"]["observation"] = str(path)
    changed["composition_probe"]["observation_sha256"] = hashlib.sha256(
        path.read_bytes()
    ).hexdigest()
    try:
        yield changed
    finally:
        directory.chmod(0o755)
        temporary.cleanup()


class FibCoprimePremisePlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = json.loads(MODULE.MANIFEST.read_text())

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.manifest)

    def test_historical_tool_identity_survives_current_api_evolution(self) -> None:
        probe = self.manifest["composition_probe"]
        commit = self.manifest["implementation"]["evidence_commit"]
        self.assertEqual(
            MODULE.git_blob_sha256(commit, probe["api"]), probe["api_sha256"]
        )
        self.assertNotEqual(MODULE.sha256(ROOT / probe["api"]), probe["api_sha256"])
        with self.assertRaisesRegex(MODULE.PlanError, "full Git object ID"):
            MODULE.git_blob_sha256(commit[:12], probe["api"])
        with self.assertRaisesRegex(MODULE.PlanError, "repository-relative"):
            MODULE.git_blob_sha256(commit, "../outside")

    def test_probe_and_authority_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["composition_probe"]["first_conflict"] = "Nat"
        with self.assertRaisesRegex(MODULE.PlanError, "semantics"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_probe"][
            "kernel_type_shape_compatible_content_mismatches"
        ] = 9
        with self.assertRaisesRegex(MODULE.PlanError, "semantics"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["authority"]["kernel_submissions"] = 4
        with self.assertRaisesRegex(MODULE.PlanError, "authority"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_probe"]["api_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "API"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["implementation"]["nat_mod_lt_sources"][0]["sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "alignment implementation"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["implementation"]["bool_constructor_order"].reverse()
        with self.assertRaisesRegex(MODULE.PlanError, "alignment implementation"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["implementation"]["evidence_commit"] = "0" * 40
        with self.assertRaisesRegex(MODULE.PlanError, "alignment implementation"):
            MODULE.validate(changed)

    def test_bool_overlap_and_next_boundary_mutations_are_rejected(self) -> None:
        observation = json.loads(
            pathlib.Path(self.manifest["composition_probe"]["observation"]).read_text()
        )
        source = observation["source"]
        source["exact_overlap_names"].remove("Bool.true")
        source["exact_overlap_names"].append("And")
        source["exact_overlap_names"].sort()
        source["alpha_type_compatible_content_mismatched_names"].remove("And")
        source["alpha_type_compatible_content_mismatched_names"].append("Bool.true")
        source["alpha_type_compatible_content_mismatched_names"].sort()
        with pinned_observation(self.manifest, observation) as changed:
            with self.assertRaisesRegex(MODULE.PlanError, "overlap partition"):
                MODULE.validate(changed)

        observation = json.loads(
            pathlib.Path(self.manifest["composition_probe"]["observation"]).read_text()
        )
        observation["source"]["structural_mismatch_control"]["error"] = (
            observation["source"]["structural_mismatch_control"]["error"].replace(
                'name: "Nat.div_mod_exec"', 'name: "Nat.mod"'
            )
        )
        with pinned_observation(self.manifest, observation) as changed:
            with self.assertRaisesRegex(MODULE.PlanError, "composition result"):
                MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_result"]["negative_control_error_kind"] = "KernelError"
        with self.assertRaisesRegex(MODULE.PlanError, "composition result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_result"]["negative_control_environment_sha256"] = (
            "0" * 64
        )
        with self.assertRaisesRegex(MODULE.PlanError, "composition result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_result"][
            "negative_control_missing_nat_div_mod_exec_direct_consumers"
        ] = []
        with self.assertRaisesRegex(MODULE.PlanError, "composition result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_probe"]["imported_division_declaration_names"].append(
            "Nat.div"
        )
        with self.assertRaisesRegex(MODULE.PlanError, "semantics"):
            MODULE.validate(changed)

    def test_official_support_audit_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["official_support_audit"]["theorems"]["Nat.dvd_mod_iff"][
            "axiom_footprint"
        ] = []
        with self.assertRaisesRegex(MODULE.PlanError, "official support audit"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["official_support_audit"]["manifest_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "changed or is mutable"):
            MODULE.validate(changed)

    def test_official_equation_pack_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["official_equation_pack"]["added_theorems"]["Nat.mod.eq_2"][
            "axiom_footprint"
        ] = ["propext"]
        with self.assertRaisesRegex(MODULE.PlanError, "equation theorem"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["official_equation_pack"]["source_closure_count"] = 182
        with self.assertRaisesRegex(MODULE.PlanError, "identity or authority"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["official_equation_pack"]["manifest_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "changed or is mutable"):
            MODULE.validate(changed)

    def test_nat_mod_invariant_pack_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["nat_mod_invariant_pack"]["manifest_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "changed or is mutable"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["nat_mod_invariant_pack"]["target"]["axiom_footprint"] = [
            "propext"
        ]
        with self.assertRaisesRegex(MODULE.PlanError, "specialization result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["nat_mod_invariant_pack"][
            "specialization_receipt_sha256"
        ] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "specialization result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["nat_mod_invariant_pack"]["authored_source_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "identity or authority"):
            MODULE.validate(changed)

    def test_nat_gcd_target_leaf_frontier_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["nat_gcd_target_leaf_frontier"]["manifest_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "changed or is mutable"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["nat_gcd_target_leaf_frontier"]["two_leaves"][
            "source_closure"
        ] = 58
        with self.assertRaisesRegex(MODULE.PlanError, "probe result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["nat_gcd_target_leaf_frontier"]["two_leaves"][
            "contains_nat_div_mod_exec"
        ] = True
        with self.assertRaisesRegex(MODULE.PlanError, "probe result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["nat_gcd_target_leaf_frontier"]["official_support"][
            "Nat.gcd_succ"
        ]["axiom_footprint"] = []
        with self.assertRaisesRegex(MODULE.PlanError, "official support"):
            MODULE.validate(changed)

    def test_nat_gcd_succ_bridge_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["nat_gcd_succ_bridge"]["manifest_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "changed or is mutable"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["nat_gcd_succ_bridge"]["gcd_succ_axiom_footprint"] = [
            "Quot.sound"
        ]
        with self.assertRaisesRegex(MODULE.PlanError, "result or authority"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["nat_gcd_succ_bridge"]["dvd_gcd"]["outcome"] = "declined"
        with self.assertRaisesRegex(MODULE.PlanError, "result or authority"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["nat_gcd_succ_bridge"]["fresh_full_runs"] = 1
        with self.assertRaisesRegex(MODULE.PlanError, "result or authority"):
            MODULE.validate(changed)

    def test_fibonacci_support_surface_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["fibonacci_support_surface"]["manifest_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "changed or is mutable"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["fibonacci_support_surface"]["roots"].pop()
        with self.assertRaisesRegex(MODULE.PlanError, "identity or result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["fibonacci_support_surface"]["axiom_footprints"] = ["propext"]
        with self.assertRaisesRegex(MODULE.PlanError, "identity or result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["fibonacci_support_surface"]["exact_target_theorem_admitted"] = True
        with self.assertRaisesRegex(MODULE.PlanError, "identity or result"):
            MODULE.validate(changed)

    def test_exact_fibonacci_coprimality_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["exact_fibonacci_coprimality"]["manifest_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "changed or is mutable"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["exact_fibonacci_coprimality"]["axiom_footprint"] = [
            "Quot.sound"
        ]
        with self.assertRaisesRegex(MODULE.PlanError, "result changed"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["exact_fibonacci_coprimality"]["proof_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "result changed"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["exact_fibonacci_coprimality"][
            "semantic_theorem_receipts_issued"
        ] = 1
        with self.assertRaisesRegex(MODULE.PlanError, "authority changed"):
            MODULE.validate(changed)

    def test_fibonacci_receipt_authority_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["fibonacci_receipt_authority"]["manifest_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "changed or is mutable"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["fibonacci_receipt_authority"]["direct_theorem_dependencies"][0][
            "content_sha256"
        ] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "identity or result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["fibonacci_receipt_authority"][
            "semantic_theorem_receipts_issued"
        ] = 1
        with self.assertRaisesRegex(MODULE.PlanError, "boundary changed"):
            MODULE.validate(changed)

    def test_native_fib_composition_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["native_fib_composition"]["manifest_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "changed or is mutable"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["native_fib_composition"]["nat_fib_declaration_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "native Fibonacci composition"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["native_fib_composition"]["r080"]["added_definitions"] = 18
        with self.assertRaisesRegex(MODULE.PlanError, "r080-native-recurrence"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["native_fib_composition"]["native_recurrence_axiom_footprint"] = [
            "Quot.sound"
        ]
        with self.assertRaisesRegex(MODULE.PlanError, "assurance"):
            MODULE.validate(changed)

    def test_native_fib_coprimality_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["native_fib_coprimality"]["manifest_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "changed or is mutable"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["native_fib_coprimality"]["proof_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "theorem changed"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["native_fib_coprimality"]["direct_theorem_dependencies"].pop()
        with self.assertRaisesRegex(MODULE.PlanError, "theorem changed"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["native_fib_coprimality"]["semantic_transport_authorized"] = True
        with self.assertRaisesRegex(MODULE.PlanError, "target boundary"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["native_fib_coprimality"]["semantic_theorem_receipts_issued"] = 1
        with self.assertRaisesRegex(MODULE.PlanError, "target boundary"):
            MODULE.validate(changed)

    def test_nat_mod_lt_compatibility_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["nat_mod_lt_compatibility_result"]["source_declaration_sha256"] = (
            "0" * 64
        )
        with self.assertRaisesRegex(MODULE.PlanError, "Nat.mod_lt"):
            MODULE.validate(changed)

        observation = json.loads(
            pathlib.Path(self.manifest["composition_probe"]["observation"]).read_text()
        )
        observation["source"]["mod_lt_compatibility_control"]["compatibility"] = (
            "kernel-type-shape"
        )
        with pinned_observation(self.manifest, observation) as changed:
            with self.assertRaisesRegex(MODULE.PlanError, "Nat.mod_lt"):
                MODULE.validate(changed)

        observation = json.loads(
            pathlib.Path(self.manifest["composition_probe"]["observation"]).read_text()
        )
        for row in observation["source"]["type_mismatched_overlaps"]:
            if row["name"] == "Nat.mod_lt":
                row["native_kernel_type_shape_sha256"] = "0" * 64
                break
        with pinned_observation(self.manifest, observation) as changed:
            with self.assertRaisesRegex(MODULE.PlanError, "Nat.mod_lt"):
                MODULE.validate(changed)

    def test_required_surface_mutation_is_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["proof_plan"]["required_native_declarations"][0] = "Nat.rec"
        with self.assertRaisesRegex(MODULE.PlanError, "semantics"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["target"]["sole_admitted_theorem_premise"] = "F:unreviewed"
        with self.assertRaisesRegex(MODULE.PlanError, "premise"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["closure_census"]["first_dependency_count"] = 9
        with self.assertRaisesRegex(MODULE.PlanError, "closure census"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_result"]["added_theorem_names"].pop()
        with self.assertRaisesRegex(MODULE.PlanError, "composition result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["singleton_inductive_result"]["added_singleton_inductives"][0][
            "constructors"
        ] = []
        with self.assertRaisesRegex(MODULE.PlanError, "singleton inductive"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["acc_inductive_result"]["added_singleton_inductives"][0][
            "constructors"
        ] = []
        with self.assertRaisesRegex(MODULE.PlanError, "Acc inductive"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["implementation"]["acc_package"]["source_declaration_sha256"][
            "Acc.rec"
        ] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "Acc inductive identity"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_result"]["receipt_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "composition result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_result"]["reused_exact_declarations"] = 3
        with self.assertRaisesRegex(MODULE.PlanError, "composition result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_result"]["reused_compatibility"][
            "translated-definitional-equality"
        ] = 1
        with self.assertRaisesRegex(MODULE.PlanError, "composition result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["definition_result"]["added_definitions"][0][
            "target_declaration_sha256"
        ] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "definition composition"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["definition_result"]["added_definitions"][1]["reducibility"] = (
            "regular:3"
        )
        with self.assertRaisesRegex(MODULE.PlanError, "definition composition"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["definition_result"]["reused_compatibility"][
            "translated-definitional-equality"
        ] = 3
        with self.assertRaisesRegex(MODULE.PlanError, "definition composition"):
            MODULE.validate(changed)


if __name__ == "__main__":
    unittest.main()
