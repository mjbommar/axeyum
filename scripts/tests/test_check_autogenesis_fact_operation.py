#!/usr/bin/env python3
"""Mutation controls for replaying typed Autogenesis fact evidence."""

from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-fact-operation.py"
SPEC = importlib.util.spec_from_file_location("check_autogenesis_fact_operation", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
checker = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checker)


class FactOperationReplayTests(unittest.TestCase):
    def setUp(self) -> None:
        registry_module = checker.load_module("registry_for_test", checker.REGISTRY_SCRIPT)
        registry = registry_module.load_registry()
        self.operation = next(
            operation for operation in registry["operations"] if operation["scope"] == "authoritative"
        )
        admission = self.operation["admission"]
        executor = self.operation["executor"]
        binding = {
            "id": self.operation["id"],
            "operation_sha256": checker.digest(self.operation),
            "registry_sha256_at_execution": "a" * 64,
            "execution_sha256": "b" * 64,
            "frontier_sha256": "c" * 64,
            "input_artifact": executor["input_artifact"],
            "input_artifact_sha256": checker.byte_digest(
                (ROOT / executor["input_artifact"]).read_bytes()
            ),
        }
        self.fact = {
            "id": "F:no-integer-square-is-minus-one",
            "statement": "There is no integer x with x * x = -1.",
            "epistemic_status": admission["epistemic_status"],
            "proof_route": admission["proof_route"],
            "axiom_footprint": admission["axiom_footprint"],
            "evidence": [
                {
                    "kind": admission["evidence_kind"],
                    "supports": "There is no integer x with x * x = -1.",
                    "check_status": "checked",
                    "checker_command": checker.checker_command(
                        "F:no-integer-square-is-minus-one"
                    ),
                    "checker_operation": binding,
                }
            ],
        }
        self.observation = {
            "verdict": "unsat",
            "evidence_label": executor["expected_evidence_label"],
            "certified": True,
            "recheck": "na",
            "arena": "ok",
        }

    def check(self, fact=None, observation=None):
        return checker.check_fact(
            fact or self.fact,
            lambda _operation: observation or self.observation,
        )

    def test_registered_fact_operation_replays(self) -> None:
        result = self.check()
        self.assertEqual(result["operation_id"], self.operation["id"])

    def test_binding_and_admission_mutations_reject(self) -> None:
        mutations = (
            ("binding", "operation_sha256", "d" * 64),
            ("binding", "input_artifact_sha256", "e" * 64),
            ("fact", "proof_route", "smt-clausal"),
            ("fact", "axiom_footprint", ["invented"]),
            ("row", "checker_command", "true"),
        )
        for target, field, value in mutations:
            with self.subTest(target=target, field=field):
                changed = copy.deepcopy(self.fact)
                if target == "binding":
                    changed["evidence"][0]["checker_operation"][field] = value
                elif target == "row":
                    changed["evidence"][0][field] = value
                else:
                    changed[field] = value
                with self.assertRaises(checker.FactOperationError):
                    self.check(changed)

    def test_failed_fresh_arena_observation_rejects(self) -> None:
        changed = dict(self.observation)
        changed["arena"] = "FAIL"
        with self.assertRaisesRegex(checker.FactOperationError, "no longer replays"):
            self.check(observation=changed)


if __name__ == "__main__":
    unittest.main()
