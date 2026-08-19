#!/usr/bin/env python3
"""Mutation controls for the typed Autogenesis operation registry."""

from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/validate-autogenesis-operations.py"
SPEC = importlib.util.spec_from_file_location("validate_autogenesis_operations", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
registry_module = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(registry_module)


class OperationRegistryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.registry = json.loads(
            (ROOT / "artifacts/autogenesis/operations.json").read_text()
        )

    def test_committed_registry_has_one_fixture_and_five_authoritative_operations(self) -> None:
        registry_module.validate_registry(self.registry, ROOT)
        self.assertEqual(len(self.registry["operations"]), 6)
        self.assertEqual(
            self.registry["operations"][0]["scope"], "counterfactual-fixture-only"
        )
        authoritative = self.registry["operations"][1]
        self.assertEqual(authoritative["scope"], "authoritative")
        self.assertEqual(
            authoritative["applicability"]["fact_ids"],
            ["F:no-integer-square-is-minus-one"],
        )
        self.assertEqual(
            authoritative["executor"]["driver"],
            "axeyum-bench/smtcomp-evidence-v1",
        )
        kernel = self.registry["operations"][2]
        self.assertEqual(kernel["scope"], "authoritative")
        self.assertEqual(kernel["applicability"]["fact_ids"], ["F:nat-zero-add"])
        self.assertEqual(
            kernel["executor"]["driver"],
            "axeyum-lean-kernel/nat-zero-add-induction-v1",
        )
        apply = self.registry["operations"][3]
        self.assertEqual(apply["scope"], "authoritative")
        self.assertEqual(apply["applicability"]["fact_ids"], ["F:nat-mul-one"])
        self.assertEqual(
            apply["executor"]["driver"],
            "axeyum-lean-kernel/nat-mul-one-episode-apply-v1",
        )
        reflexivity = self.registry["operations"][4]
        self.assertEqual(
            reflexivity["applicability"]["fact_ids"],
            ["F:ml430-nat-ascfactorial-zero-fd183202"],
        )
        self.assertEqual(
            reflexivity["executor"]["driver"],
            "axeyum-lean-import/statement-reflexivity-v1",
        )
        desc_reflexivity = self.registry["operations"][5]
        self.assertEqual(
            desc_reflexivity["applicability"]["fact_ids"],
            ["F:ml430-nat-descfactorial-zero-966b01df"],
        )
        self.assertEqual(
            desc_reflexivity["executor"]["driver"],
            "axeyum-lean-import/statement-reflexivity-v1",
        )

    def test_duplicate_operation_id_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"].append(copy.deepcopy(mutated["operations"][0]))
        with self.assertRaisesRegex(registry_module.RegistryError, "duplicate"):
            registry_module.validate_registry(mutated, ROOT)

    def test_shell_command_field_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][0]["checker"]["command"] = "true"
        with self.assertRaisesRegex(registry_module.RegistryError, "fields differ"):
            registry_module.validate_registry(mutated, ROOT)

    def test_missing_implementation_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][0]["producer"]["implementation"] = "missing.py"
        with self.assertRaisesRegex(registry_module.RegistryError, "does not exist"):
            registry_module.validate_registry(mutated, ROOT)

    def test_unknown_route_evidence_pair_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][1]["admission"]["proof_route"] = "smt-clausal"
        with self.assertRaisesRegex(registry_module.RegistryError, "outside the v1"):
            registry_module.validate_registry(mutated, ROOT)

    def test_authoritative_operation_requires_a_typed_executor(self) -> None:
        mutated = copy.deepcopy(self.registry)
        del mutated["operations"][1]["executor"]
        with self.assertRaisesRegex(registry_module.RegistryError, "missing=.*executor"):
            registry_module.validate_registry(mutated, ROOT)

    def test_gate_review_and_kernel_executor_scope_are_exact(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][2]["reviewed_gate_mentions"] = []
        registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][2]["reviewed_gate_mentions"].append("missing.sh")
        with self.assertRaisesRegex(registry_module.RegistryError, "gate mention"):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][2]["executor"]["target_theorem"] = "Nat.add_zero"
        with self.assertRaisesRegex(registry_module.RegistryError, "target"):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][3]["executor"]["premise_operation_id"] = "invented"
        with self.assertRaisesRegex(registry_module.RegistryError, "premise_operation"):
            registry_module.validate_registry(mutated, ROOT)

    def test_executor_cannot_escape_or_name_an_unknown_driver(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][1]["executor"]["input_artifact"] = "../secret.smt2"
        with self.assertRaisesRegex(registry_module.RegistryError, "repository-relative"):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][1]["executor"]["driver"] = "shell"
        with self.assertRaisesRegex(registry_module.RegistryError, "unsupported"):
            registry_module.validate_registry(mutated, ROOT)

    def test_executor_fact_and_artifact_must_match_applicability(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][1]["executor"]["input_fact_id"] = "F:contraposition"
        with self.assertRaisesRegex(registry_module.RegistryError, "sole applicable"):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][1]["executor"]["input_artifact"] = (
            "artifacts/facts/smt2/neg-contraposition.smt2"
        )
        with self.assertRaisesRegex(registry_module.RegistryError, "does not match"):
            registry_module.validate_registry(mutated, ROOT)

    def test_admission_footprint_must_match_its_policy(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][1]["admission"]["axiom_footprint"] = []
        with self.assertRaisesRegex(registry_module.RegistryError, "violates"):
            registry_module.validate_registry(mutated, ROOT)

    def test_statement_reflexivity_driver_is_exactly_manifest_bound(self) -> None:
        for field, value in (
            ("target_definition", "Axeyum.Wrong"),
            ("max_binders", 9),
            ("max_constructed_nodes", 17),
        ):
            with self.subTest(field=field):
                mutated = copy.deepcopy(self.registry)
                mutated["operations"][4]["executor"][field] = value
                with self.assertRaisesRegex(registry_module.RegistryError, "manifests disagree"):
                    registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][0]["admission"]["axiom_footprint"] = ["invented"]
        with self.assertRaisesRegex(registry_module.RegistryError, "violates"):
            registry_module.validate_registry(mutated, ROOT)


if __name__ == "__main__":
    unittest.main()
