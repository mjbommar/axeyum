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

    def test_committed_registry_has_one_fixture_and_one_authoritative_operation(self) -> None:
        registry_module.validate_registry(self.registry, ROOT)
        self.assertEqual(len(self.registry["operations"]), 2)
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

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][0]["admission"]["axiom_footprint"] = ["invented"]
        with self.assertRaisesRegex(registry_module.RegistryError, "violates"):
            registry_module.validate_registry(mutated, ROOT)


if __name__ == "__main__":
    unittest.main()
