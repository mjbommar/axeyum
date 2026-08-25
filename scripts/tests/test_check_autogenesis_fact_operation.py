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

    def test_episode_local_apply_binding_and_result_replay(self) -> None:
        registry = checker.load_module(
            "registry_for_apply_replay_test", checker.REGISTRY_SCRIPT
        ).load_registry()
        operation = registry["operations"][3]
        executor = operation["executor"]
        trigger = {
            "premise_fact_id": executor["premise_fact_id"],
            "premise_operation_id": executor["premise_operation_id"],
            "premise_source_commit": "0" * 40,
            "premise_before_fact_sha256": "1" * 64,
            "premise_after_fact_sha256": "2" * 64,
            "premise_execution_sha256": "3" * 64,
            "premise_transaction_sha256": "4" * 64,
            "premise_admission_event_sha256": "5" * 64,
            "readiness_delta_sha256": "6" * 64,
            "frontier_after_sha256": "7" * 64,
        }
        statement = (
            "theorem Nat.mul_one : ((x0 : AxNat) -> Eq.{1} AxNat "
            "(AxNat.mul x0 (AxNat.succ AxNat.zero)) x0)"
        )
        binding = {
            "id": operation["id"],
            "operation_sha256": checker.digest(operation),
            "registry_sha256_at_execution": "a" * 64,
            "execution_sha256": "b" * 64,
            "frontier_sha256": trigger["frontier_after_sha256"],
            "target_theorem": executor["target_theorem"],
            "formal_statement_sha256": checker.byte_digest(statement.encode()),
            "premise_fact_id": executor["premise_fact_id"],
            "premise_operation_id": executor["premise_operation_id"],
            "premise_budget": executor["premise_budget"],
            "budget": executor["budget"],
            "trigger": trigger,
        }
        fact = {
            "id": "F:nat-mul-one",
            "statement": "mul one",
            "formal": {"statement": statement},
            "epistemic_status": "proved",
            "proof_route": "kernel-lean",
            "axiom_footprint": [],
            "evidence": [
                {
                    "kind": "kernel-term",
                    "supports": "mul one",
                    "check_status": "checked",
                    "checker_command": checker.checker_command("F:nat-mul-one"),
                    "checker_operation": binding,
                }
            ],
        }
        observation = {
            "verdict": "proved",
            "evidence_label": executor["expected_evidence_label"],
            "canonical_type": checker.formal_type(fact),
            "axiom_footprint": [],
            "retained_answer_dependencies": [],
            "episode_dependency": "Autogenesis.Authoritative.E1111111111111111.premise",
            "attempted": 1,
            "accepted_plan_rank": 1,
            "premise_attempted": 2,
            "premise_plan_rank": 2,
        }
        result = checker.check_fact(fact, lambda _operation, _trigger: observation)
        self.assertEqual(result["operation_id"], operation["id"])

        changed = copy.deepcopy(fact)
        changed["evidence"][0]["checker_operation"]["trigger"][
            "frontier_after_sha256"
        ] = "8" * 64
        with self.assertRaisesRegex(checker.FactOperationError, "trigger"):
            checker.check_fact(changed, lambda _operation, _trigger: observation)

    def test_statement_reflexivity_binding_and_result_replay(self) -> None:
        registry = checker.load_module(
            "registry_for_reflexivity_replay_test", checker.REGISTRY_SCRIPT
        ).load_registry()
        operation = registry["operations"][4]
        executor = operation["executor"]
        adapter = checker.json.loads(
            (ROOT / executor["statement_adapter_manifest"]).read_text()
        )
        reflexivity = checker.json.loads(
            (ROOT / executor["reflexivity_manifest"]).read_text()
        )
        evidence = reflexivity["operation"]
        statement = "∀ (n : ℕ), n.ascFactorial 0 = 1"
        binding = {
            "id": operation["id"],
            "operation_sha256": checker.digest(operation),
            "registry_sha256_at_execution": "a" * 64,
            "execution_sha256": "b" * 64,
            "frontier_sha256": "c" * 64,
            "statement_adapter_manifest": executor["statement_adapter_manifest"],
            "statement_adapter_manifest_sha256": checker.digest(adapter),
            "reflexivity_manifest": executor["reflexivity_manifest"],
            "reflexivity_manifest_sha256": checker.digest(reflexivity),
            "external_artifact_sha256": adapter["external_artifact"]["sha256"],
            "formal_statement_sha256": checker.byte_digest(statement.encode()),
            "target_definition": executor["target_definition"],
            "goal_sha256": evidence["goal_sha256"],
            "proof_sha256": evidence["proof_sha256"],
            "target_content_sha256": evidence["target_content_sha256"],
            "max_binders": executor["max_binders"],
            "max_constructed_nodes": executor["max_constructed_nodes"],
        }
        fact = {
            "id": "F:ml430-nat-ascfactorial-zero-fd183202",
            "statement": "ascFactorial zero",
            "formal": {"statement": statement},
            "epistemic_status": "proved",
            "proof_route": "kernel-lean",
            "axiom_footprint": [],
            "evidence": [
                {
                    "kind": "kernel-term",
                    "supports": "ascFactorial zero",
                    "check_status": "checked",
                    "checker_command": checker.checker_command(
                        "F:ml430-nat-ascfactorial-zero-fd183202"
                    ),
                    "checker_operation": binding,
                }
            ],
        }
        observation = {
            "verdict": "proved",
            "evidence_label": executor["expected_evidence_label"],
            "goal_sha256": evidence["goal_sha256"],
            "proof_sha256": evidence["proof_sha256"],
            "target_content_sha256": evidence["target_content_sha256"],
            "external_artifact_sha256": adapter["external_artifact"]["sha256"],
            "binders": evidence["binders"],
            "constructed_nodes": evidence["constructed_nodes"],
            "max_binders": evidence["max_binders"],
            "max_constructed_nodes": evidence["max_constructed_nodes"],
            "admitted_declarations": evidence["admitted_declarations"],
            "axiom_footprint": [],
            "retained_answer_dependencies": [],
            "target_dependency": False,
            "ledger_writes": 0,
        }
        result = checker.check_fact(fact, lambda _operation: observation)
        self.assertEqual(result["operation_id"], operation["id"])

        changed = copy.deepcopy(fact)
        changed["evidence"][0]["checker_operation"]["proof_sha256"] = "0" * 64
        with self.assertRaisesRegex(checker.FactOperationError, "stale or mutated"):
            checker.check_fact(changed, lambda _operation: observation)

    def test_modeq_family_multi_target_binding_and_result_replay(self) -> None:
        registry = checker.load_module(
            "registry_for_modeq_family_replay_test", checker.REGISTRY_SCRIPT
        ).load_registry()
        operation = next(
            op
            for op in registry["operations"]
            if op["id"] == "authoritative-mathlib-modeq-family-v1"
        )
        executor = operation["executor"]
        executor_module = checker.load_module(
            "executor_for_modeq_family_replay_test", checker.EXECUTOR_SCRIPT
        )
        fact_id = "F:ml430-nat-modeq-symm-0a3d4d18"
        target = executor_module.resolve_multi_target(operation, fact_id)
        adapter = checker.json.loads(
            (ROOT / target["statement_adapter_manifest"]).read_text()
        )
        modeq = checker.json.loads((ROOT / target["modeq_manifest"]).read_text())
        op = modeq["operation"]
        statement = (
            "∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]"
        )
        binding = {
            "id": operation["id"],
            "operation_sha256": checker.digest(operation),
            "registry_sha256_at_execution": "a" * 64,
            "execution_sha256": "b" * 64,
            "frontier_sha256": "c" * 64,
            "target_fact_id": fact_id,
            "statement_adapter_manifest": target["statement_adapter_manifest"],
            "statement_adapter_manifest_sha256": checker.digest(adapter),
            "modeq_manifest": target["modeq_manifest"],
            "modeq_manifest_sha256": checker.digest(modeq),
            "external_artifact_sha256": adapter["external_artifact"]["sha256"],
            "formal_statement_sha256": checker.byte_digest(statement.encode()),
            "target_definition": target["target_definition"],
            "goal_sha256": op["goal_sha256"],
            "proof_sha256": op["proof_sha256"],
            "target_content_sha256": op["target_content_sha256"],
            "binders_used": op["binders_used"],
            "max_binders": op["max_binders"],
            "admitted_declarations": op["admitted_declarations"],
        }
        fact = {
            "id": fact_id,
            "statement": "modeq symm",
            "formal": {"statement": statement},
            "epistemic_status": "proved",
            "proof_route": "kernel-lean",
            "axiom_footprint": [],
            "evidence": [
                {
                    "kind": "kernel-term",
                    "supports": "modeq symm",
                    "check_status": "checked",
                    "checker_command": checker.checker_command(fact_id),
                    "checker_operation": binding,
                }
            ],
        }
        observation = {
            "verdict": "proved",
            "evidence_label": executor["expected_evidence_label"],
            "target_definition": target["target_definition"],
            "goal_sha256": op["goal_sha256"],
            "proof_sha256": op["proof_sha256"],
            "target_content_sha256": op["target_content_sha256"],
            "binders_used": op["binders_used"],
            "max_binders": op["max_binders"],
            "admitted_declarations": op["admitted_declarations"],
            "axiom_footprint": [],
            "retained_answer_dependencies": [],
            "target_dependency": False,
            "ledger_writes": 0,
        }
        result = checker.check_fact(
            fact, lambda _operation, fact=None: observation
        )
        self.assertEqual(result["operation_id"], operation["id"])

        # Cross-target replay: relabeling the binding's target_fact_id (and
        # every field a fresh `resolve_multi_target` on the sibling would
        # disagree with) to a sibling fact must be refused, not silently
        # accepted -- this is the same guard ADR-0554 demonstrates on the
        # execution receipt, one layer up at the settled-fact evidence row.
        sibling_id = "F:ml430-nat-modeq-trans-ef9d1c46"
        changed = copy.deepcopy(fact)
        changed["evidence"][0]["checker_operation"]["target_fact_id"] = sibling_id
        with self.assertRaisesRegex(checker.FactOperationError, "stale or mutated"):
            checker.check_fact(changed, lambda _operation, fact=None: observation)

        changed = copy.deepcopy(fact)
        changed["evidence"][0]["checker_operation"]["proof_sha256"] = "0" * 64
        with self.assertRaisesRegex(checker.FactOperationError, "stale or mutated"):
            checker.check_fact(changed, lambda _operation, fact=None: observation)


if __name__ == "__main__":
    unittest.main()
