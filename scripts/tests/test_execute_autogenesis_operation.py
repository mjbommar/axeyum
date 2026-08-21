#!/usr/bin/env python3
"""Mutation controls for authoritative Autogenesis operation execution."""

from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import tempfile
import unittest
from unittest import mock


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/execute-autogenesis-operation.py"
SPEC = importlib.util.spec_from_file_location("execute_autogenesis_operation", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
execution = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(execution)

REFLEXIVITY_FACT = "F:ml430-nat-descfactorial-zero-966b01df"
FIB_FACT = "F:ml430-nat-fib-add-two-b86e0c82"
FIB_COPRIME_FACT = "F:ml430-nat-fib-coprime-fib-succ-162fc738"
GCD_GREATEST_FACT = "F:ml430-nat-gcd-greatest-0a04214a"


def settle_reflexivity_fact(facts):
    for fact_id in (
        REFLEXIVITY_FACT,
        FIB_FACT,
        FIB_COPRIME_FACT,
        GCD_GREATEST_FACT,
    ):
        target = copy.deepcopy(facts[fact_id])
        target["epistemic_status"] = "proved"
        facts[fact_id] = target


class OperationExecutionTests(unittest.TestCase):
    def setUp(self) -> None:
        frontier_module = execution.load_module("frontier_for_test", execution.FRONTIER_SCRIPT)
        self.facts = frontier_module.load()
        settle_reflexivity_fact(self.facts)
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

    def episode_trigger_inputs(self):
        frontier_module = execution.load_module(
            "frontier_for_episode_test", execution.FRONTIER_SCRIPT
        )
        facts = frontier_module.load()
        settle_reflexivity_fact(facts)
        for fact_id in ("F:nat-zero-add", "F:nat-mul-one"):
            target = copy.deepcopy(facts[fact_id])
            target["epistemic_status"] = "open"
            target["evidence"] = []
            target.pop("proof_route", None)
            target.pop("axiom_footprint", None)
            facts[fact_id] = target
        registry = execution.load_module(
            "registry_for_episode_test", execution.REGISTRY_SCRIPT
        ).load_registry()
        before_frontier = frontier_module.build_machine_frontier(facts, registry)
        before, premise_operation, _ = execution.selected_inputs(before_frontier, facts)
        premise_observation = {
            "verdict": "proved",
            "evidence_label": "kernel-term-axiom-free",
            "canonical_type": execution.formal_type(before),
            "axiom_footprint": [],
            "retained_answer_dependencies": [],
            "attempted": 2,
            "accepted_plan_rank": 2,
        }
        premise_execution = execution.build_receipt(
            frontier=before_frontier,
            fact=before,
            operation=premise_operation,
            registry=registry,
            git_commit="d" * 40,
            observation=premise_observation,
        )
        prepare = execution.load_module(
            "prepare_for_episode_test",
            execution.ROOT / "scripts/prepare-autogenesis-fact-transaction.py",
        )
        transaction = prepare.build_authoritative_transaction(
            before_fact=before,
            execution=premise_execution,
            operation=premise_operation,
            registry=registry,
        )
        apply = execution.load_module(
            "apply_for_episode_test", execution.APPLY_TRANSACTION_SCRIPT
        )
        event = apply.build_admission_event(transaction)
        facts[before["id"]] = transaction["authoritative_write"]["after_fact"]
        after_frontier = frontier_module.build_machine_frontier(facts, registry)
        self.assertEqual(
            after_frontier["selection"]["selected_fact_id"], "F:nat-mul-one"
        )
        readiness = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-readiness-delta",
            "mode": "authoritative-ledger",
            "identity": {
                "episode_id": transaction["identity"]["episode_id"],
                "transaction_sha256": transaction["transaction_sha256"],
                "execution_sha256": premise_execution["execution_sha256"],
                "durable_admission_event_sha256": event["event_sha256"],
                "before_frontier_sha256": before_frontier["frontier_sha256"],
                "after_frontier_sha256": after_frontier["frontier_sha256"],
            },
            "frontier_change": {
                "selected_before": "F:nat-zero-add",
                "selected_after": "F:nat-mul-one",
                "no_longer_ready": ["F:nat-zero-add"],
            },
            "newly_ready": ["F:nat-mul-one"],
            "cause": {
                "event_type": "fact-admitted",
                "admitted_fact_id": "F:nat-zero-add",
            },
            "authoritative_ledger_writes": 1,
            "fixture_writes": 0,
        }
        readiness["readiness_delta_sha256"] = execution.digest(readiness)
        return (
            facts,
            registry,
            before_frontier,
            after_frontier,
            premise_execution,
            transaction,
            event,
            readiness,
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
        settle_reflexivity_fact(facts)
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

    def test_episode_trigger_chain_uniquely_authorizes_a(self) -> None:
        (
            facts,
            registry,
            before_frontier,
            frontier,
            premise_execution,
            transaction,
            event,
            readiness,
        ) = self.episode_trigger_inputs()
        operation = registry["operations"][3]
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            for name, value in (
                ("frontier-before.json", before_frontier),
                ("execution.json", premise_execution),
                ("transaction.json", transaction),
                ("admission-event.json", event),
                ("readiness.json", readiness),
            ):
                (root / name).write_text(json.dumps(value))
            original_load = execution.load_module

            class FakeReadiness:
                class ReadinessError(RuntimeError):
                    pass

                @staticmethod
                def repository_inputs_from_execution(_execution):
                    return {}, registry

                @staticmethod
                def build_authoritative_delta(**_kwargs):
                    return readiness

            def load_for_test(name, path):
                if path == execution.READINESS_SCRIPT:
                    return FakeReadiness
                return original_load(name, path)

            with mock.patch.object(execution, "load_module", side_effect=load_for_test):
                trigger = execution.load_episode_trigger(
                    bundle=root,
                    frontier=frontier,
                    facts=facts,
                    registry=registry,
                    operation=operation,
                )
            self.assertEqual(trigger["premise_fact_id"], "F:nat-zero-add")
            observation = {
                "verdict": "proved",
                "evidence_label": operation["executor"]["expected_evidence_label"],
                "canonical_type": execution.formal_type(facts["F:nat-mul-one"]),
                "axiom_footprint": [],
                "retained_answer_dependencies": [],
                "episode_dependency": execution.theorem_candidate(
                    trigger["premise_before_fact_sha256"], "premise"
                ),
                "attempted": 1,
                "accepted_plan_rank": 1,
                "premise_attempted": 2,
                "premise_plan_rank": 2,
            }
            receipt = execution.build_receipt(
                frontier=frontier,
                fact=facts["F:nat-mul-one"],
                operation=operation,
                registry=registry,
                git_commit="e" * 40,
                observation=observation,
                trigger=trigger,
            )
            self.assertEqual(receipt["identity"]["trigger"], trigger)

            readiness["newly_ready"] = []
            readiness["readiness_delta_sha256"] = execution.digest(
                {k: v for k, v in readiness.items() if k != "readiness_delta_sha256"}
            )
            (root / "readiness.json").write_text(json.dumps(readiness))
            with mock.patch.object(execution, "load_module", side_effect=load_for_test):
                with self.assertRaisesRegex(
                    execution.ExecutionError, "stale or mutated|uniquely authorize"
                ):
                    execution.load_episode_trigger(
                        bundle=root,
                        frontier=frontier,
                        facts=facts,
                        registry=registry,
                        operation=operation,
                    )

    def test_apply_evidence_parser_is_closed(self) -> None:
        with self.assertRaisesRegex(execution.ExecutionError, "wrong kind"):
            execution.parse_apply_evidence("wrong\n")

    def test_statement_reflexivity_receipt_binds_manifests_artifact_and_proof(self) -> None:
        frontier_module = execution.load_module(
            "frontier_for_reflexivity_execution_test", execution.FRONTIER_SCRIPT
        )
        facts = frontier_module.load()
        settle_reflexivity_fact(facts)
        target = copy.deepcopy(facts[REFLEXIVITY_FACT])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        facts[REFLEXIVITY_FACT] = target
        frontier = frontier_module.build_machine_frontier(facts)
        fact, operation, registry = execution.selected_inputs(frontier, facts)
        self.assertEqual(fact["id"], REFLEXIVITY_FACT)
        observation = execution.expected_statement_reflexivity_observation(
            operation, fact
        )
        receipt = execution.build_receipt(
            frontier=frontier,
            fact=fact,
            operation=operation,
            registry=registry,
            git_commit="f" * 40,
            observation=observation,
        )
        self.assertEqual(
            receipt["identity"]["external_artifact_sha256"],
            observation["external_artifact_sha256"],
        )
        self.assertEqual(
            receipt["request"]["reflexivity_manifest"],
            "artifacts/autogenesis/mathlib-descfactorial-zero-reflexivity-v1.json",
        )
        changed = copy.deepcopy(observation)
        changed["proof_sha256"] = "0" * 64
        with self.assertRaisesRegex(execution.ExecutionError, "required source-bound"):
            execution.build_receipt(
                frontier=frontier,
                fact=fact,
                operation=operation,
                registry=registry,
                git_commit="f" * 40,
                observation=changed,
            )

    def test_checked_theorem_receipt_binds_archive_source_and_proof(self) -> None:
        frontier_module = execution.load_module(
            "frontier_for_checked_theorem_execution_test", execution.FRONTIER_SCRIPT
        )
        facts = frontier_module.load()
        settle_reflexivity_fact(facts)
        target = copy.deepcopy(facts[FIB_FACT])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        facts[FIB_FACT] = target
        frontier = frontier_module.build_machine_frontier(facts)
        fact, operation, registry = execution.selected_inputs(frontier, facts)
        self.assertEqual(fact["id"], FIB_FACT)
        observation = execution.expected_checked_theorem_receipt_observation(
            operation, fact
        )
        receipt = execution.build_receipt(
            frontier=frontier,
            fact=fact,
            operation=operation,
            registry=registry,
            git_commit="1" * 40,
            observation=observation,
        )
        self.assertEqual(
            receipt["identity"]["receipt_sha256"], observation["receipt_sha256"]
        )
        self.assertEqual(
            receipt["identity"]["source_artifact_sha256"],
            observation["source_artifact_sha256"],
        )
        changed = copy.deepcopy(observation)
        changed["fresh_imports"] = 1
        with self.assertRaisesRegex(execution.ExecutionError, "required source-bound"):
            execution.build_receipt(
                frontier=frontier,
                fact=fact,
                operation=operation,
                registry=registry,
                git_commit="1" * 40,
                observation=changed,
            )

    def test_dependency_theorem_receipt_binds_exact_premise_sets(self) -> None:
        frontier_module = execution.load_module(
            "frontier_for_dependency_theorem_execution_test",
            execution.FRONTIER_SCRIPT,
        )
        facts = frontier_module.load()
        settle_reflexivity_fact(facts)
        target = copy.deepcopy(facts[FIB_COPRIME_FACT])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        facts[FIB_COPRIME_FACT] = target
        frontier = frontier_module.build_machine_frontier(facts)
        fact, operation, registry = execution.selected_inputs(frontier, facts)
        self.assertEqual(fact["id"], FIB_COPRIME_FACT)
        observation = execution.expected_dependency_theorem_receipt_observation(
            operation, fact
        )
        self.assertEqual(len(observation["retained_answer_dependencies"]), 8)
        self.assertEqual(observation["transitive_theorem_dependencies"], 115)
        receipt = execution.build_receipt(
            frontier=frontier,
            fact=fact,
            operation=operation,
            registry=registry,
            git_commit="3" * 40,
            observation=observation,
        )
        self.assertEqual(
            receipt["identity"]["dependency_set_sha256"],
            operation["executor"]["dependency_set_sha256"],
        )
        for field, value in (
            ("retained_answer_dependencies", observation["retained_answer_dependencies"][:-1]),
            ("dependency_set_sha256", "0" * 64),
            ("transitive_dependency_set_sha256", "0" * 64),
        ):
            with self.subTest(field=field):
                changed = copy.deepcopy(observation)
                changed[field] = value
                with self.assertRaisesRegex(execution.ExecutionError, "required source-bound"):
                    execution.build_receipt(
                        frontier=frontier,
                        fact=fact,
                        operation=operation,
                        registry=registry,
                        git_commit="3" * 40,
                        observation=changed,
                    )


if __name__ == "__main__":
    unittest.main()
