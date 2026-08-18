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

    def test_committed_registry_is_valid_and_fixture_scoped(self) -> None:
        registry_module.validate_registry(self.registry, ROOT)
        self.assertEqual(len(self.registry["operations"]), 1)
        self.assertEqual(
            self.registry["operations"][0]["scope"], "counterfactual-fixture-only"
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


if __name__ == "__main__":
    unittest.main()
