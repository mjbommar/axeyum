#!/usr/bin/env python3
"""Mutation controls for authoritative Autogenesis operation execution."""

from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest
from unittest import mock


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/execute-autogenesis-operation.py"
SPEC = importlib.util.spec_from_file_location("execute_autogenesis_operation", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
execution = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(execution)


class OperationExecutionTests(unittest.TestCase):
    def setUp(self) -> None:
        frontier_module = execution.load_module("frontier_for_test", execution.FRONTIER_SCRIPT)
        self.facts = frontier_module.load()
        target = copy.deepcopy(self.facts["F:no-integer-square-is-minus-one"])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        self.facts[target["id"]] = target
        self.frontier = frontier_module.build_machine_frontier(self.facts)
        self.fact, self.operation, self.registry = execution.selected_inputs(
            self.frontier, self.facts
        )
        self.observation = {
            "verdict": "unsat",
            "evidence_label": "unsat-int-quadratic-negative-discriminant",
            "certified": True,
            "recheck": "na",
            "arena": "ok",
        }

    def receipt(self):
        return execution.build_receipt(
            frontier=self.frontier,
            fact=self.fact,
            operation=self.operation,
            registry=self.registry,
            git_commit="a" * 40,
            observation=self.observation,
        )

    def test_receipt_binds_selection_registry_fact_input_and_commit(self) -> None:
        receipt = self.receipt()
        identity = receipt["identity"]
        self.assertEqual(identity["fact_id"], "F:no-integer-square-is-minus-one")
        self.assertEqual(
            identity["operation_id"],
            "smt-int-quadratic-negative-discriminant-v1",
        )
        self.assertEqual(identity["frontier_sha256"], self.frontier["frontier_sha256"])
        self.assertEqual(receipt["acceptance"]["caller_authored_command"], False)
        execution.verify_receipt(receipt, receipt)

    def test_each_assurance_field_is_required(self) -> None:
        for field, value in (
            ("verdict", "unknown"),
            ("evidence_label", "unsat-uncertified"),
            ("certified", False),
            ("recheck", "FAIL"),
            ("arena", "none:uncertified-unsat"),
        ):
            with self.subTest(field=field):
                changed = dict(self.observation)
                changed[field] = value
                with self.assertRaisesRegex(execution.ExecutionError, "source-bound"):
                    execution.build_receipt(
                        frontier=self.frontier,
                        fact=self.fact,
                        operation=self.operation,
                        registry=self.registry,
                        git_commit="a" * 40,
                        observation=changed,
                    )

    def test_parser_rejects_missing_or_duplicated_evidence(self) -> None:
        with self.assertRaisesRegex(execution.ExecutionError, "observed 0"):
            execution.parse_observation("unsat\n")
        line = (
            "; evidence kind=unsat-int-quadratic-negative-discriminant "
            "certified=1 recheck=na arena=ok ms=0\n"
        )
        with self.assertRaisesRegex(execution.ExecutionError, "observed 2"):
            execution.parse_observation(line + line + "unsat\n")

    def test_rehashed_mutation_is_still_stale(self) -> None:
        expected = self.receipt()
        changed = copy.deepcopy(expected)
        changed["acceptance"]["source_bound"] = False
        changed["execution_sha256"] = execution.digest(
            {key: value for key, value in changed.items() if key != "execution_sha256"}
        )
        with self.assertRaisesRegex(execution.ExecutionError, "stale"):
            execution.verify_receipt(changed, expected)

    def test_frontier_without_one_exact_selection_refuses_execution(self) -> None:
        changed = copy.deepcopy(self.frontier)
        changed["selection"]["selected_fact_id"] = None
        changed["selection"]["admissible_fact_ids"] = []
        changed["selection"]["outcome"] = "refused-no-admissible-candidate"
        changed["frontier_sha256"] = execution.digest(
            {key: value for key, value in changed.items() if key != "frontier_sha256"}
        )
        with self.assertRaisesRegex(execution.ExecutionError, "invalid"):
            execution.selected_inputs(changed, self.facts)

    def test_authoritative_kernel_receipt_binds_formal_statement_and_axiom_free_result(self):
        frontier_module = execution.load_module(
            "frontier_for_kernel_execution_test", execution.FRONTIER_SCRIPT
        )
        facts = frontier_module.load()
        target = copy.deepcopy(facts["F:nat-zero-add"])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        facts[target["id"]] = target
        frontier = frontier_module.build_machine_frontier(facts)
        fact, operation, registry = execution.selected_inputs(frontier, facts)
        observation = {
            "verdict": "proved",
            "evidence_label": "kernel-term-axiom-free",
            "canonical_type": execution.formal_type(fact),
            "axiom_footprint": [],
            "retained_answer_dependencies": [],
            "attempted": 2,
            "accepted_plan_rank": 2,
        }
        receipt = execution.build_receipt(
            frontier=frontier,
            fact=fact,
            operation=operation,
            registry=registry,
            git_commit="b" * 40,
            observation=observation,
        )
        self.assertIn("formal_statement_sha256", receipt["identity"])
        self.assertNotIn("input_artifact_sha256", receipt["identity"])
        self.assertEqual(receipt["result"]["axiom_footprint"], [])

        changed = copy.deepcopy(observation)
        changed["canonical_type"] += " mutated"
        with self.assertRaisesRegex(execution.ExecutionError, "required"):
            execution.build_receipt(
                frontier=frontier,
                fact=fact,
                operation=operation,
                registry=registry,
                git_commit="b" * 40,
                observation=changed,
            )

    def test_authoritative_execution_rejects_ambient_executable_overrides(self) -> None:
        for variable, operation in (
            ("AXEYUM_SMTCOMP_CLI", self.operation),
            (
                "AXEYUM_AUTOGENESIS_INDUCTION_CHECK",
                execution.load_module(
                    "registry_for_override_test", execution.REGISTRY_SCRIPT
                ).load_registry()["operations"][2],
            ),
        ):
            with self.subTest(variable=variable), mock.patch.dict(
                "os.environ", {variable: "/tmp/caller-selected-executable"}, clear=False
            ):
                with self.assertRaisesRegex(execution.ExecutionError, "forbids"):
                    execution.run_registered(operation)


if __name__ == "__main__":
    unittest.main()
