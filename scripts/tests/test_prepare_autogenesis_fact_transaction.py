from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "prepare-autogenesis-fact-transaction.py"
SPEC = importlib.util.spec_from_file_location("prepare_autogenesis_fact_transaction", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

REFLEXIVITY_FACT = "F:ml430-nat-descfactorial-zero-966b01df"
FIB_FACT = "F:ml430-nat-fib-add-two-b86e0c82"
FIB_COPRIME_FACT = "F:ml430-nat-fib-coprime-fib-succ-162fc738"
GCD_GREATEST_FACT = "F:ml430-nat-gcd-greatest-0a04214a"
INT_FIB_NATCAST_FACT = "F:ml430-int-fib-natcast-d5886be4"
INT_FIB_ADD_TWO_FACT = "F:ml430-int-fib-add-two-739358dd"
INT_FIB_COROLLARY_FACT = (
    "F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d"
)


def settle_reflexivity_fact(facts):
    for fact_id in (
        REFLEXIVITY_FACT,
        FIB_FACT,
        FIB_COPRIME_FACT,
        GCD_GREATEST_FACT,
        INT_FIB_NATCAST_FACT,
        INT_FIB_ADD_TWO_FACT,
        INT_FIB_COROLLARY_FACT,
    ):
        target = copy.deepcopy(facts[fact_id])
        target["epistemic_status"] = "proved"
        facts[fact_id] = target


class FactTransactionTests(unittest.TestCase):
    def inputs(self):
        declaration = "Autogenesis.E.premise"
        before = {
            "schema_version": 1,
            "id": "F:nat-zero-add",
            "title": "zero add",
            "statement": "zero add",
            "formal": {"statement": "theorem Nat.zero_add : B"},
            "epistemic_status": "open",
            "depends_on": [],
            "evidence": [],
            "provenance": {"date": "2026-08-18"},
        }
        evidence = {
            "identity": {"fact_id": "F:nat-zero-add", "episode_id": "episode"},
            "result": {
                "outcome": "proved",
                "declaration": declaration,
                "canonical_type": "B",
            },
            "acceptance": {
                "independent_kernel_checked": True,
                "axiom_footprint": [],
                "retained_answer_dependencies": [],
            },
            "route": {
                "operation_id": "autogenesis-kernel-premise-evidence-v1",
                "operation_registry_sha256": "a" * 64,
            },
            "evidence_sha256": "evidence",
        }
        transition = {"transition_sha256": "transition"}
        event = {
            "identity": {
                "fact_id": "F:nat-zero-add",
                "premise_evidence_sha256": "evidence",
                "transition_sha256": "transition",
            },
            "event_sha256": "event",
            "authoritative_ledger_writes": [],
        }
        return before, evidence, transition, event

    def build(self):
        before, evidence, transition, event = self.inputs()
        return MODULE.build_transaction(
            before_fact=before,
            evidence=evidence,
            transition=transition,
            event=event,
            source_is_authoritative=False,
        )

    def test_prepared_delta_is_typed_and_does_not_claim_admission(self):
        transaction = self.build()
        after = transaction["authoritative_write"]["after_fact"]
        self.assertEqual(transaction["state"], "prepared")
        self.assertIsNone(transaction["admission_event"])
        self.assertEqual(after["epistemic_status"], "proved")
        self.assertEqual(after["proof_route"], "kernel-lean")
        self.assertEqual(after["axiom_footprint"], [])
        self.assertNotIn("checker_command", after["evidence"][0])
        self.assertEqual(
            after["evidence"][0]["checker_operation"]["id"],
            "autogenesis-kernel-premise-evidence-v1",
        )
        self.assertEqual(
            transaction["registered_checker_operation"]["registry_sha256"],
            "a" * 64,
        )

    def test_settled_or_evidence_bearing_precondition_rejects(self):
        for key, value, message in (
            ("epistemic_status", "proved", "not open"),
            ("evidence", [{}], "empty evidence"),
        ):
            with self.subTest(key=key):
                before, evidence, transition, event = self.inputs()
                before[key] = value
                with self.assertRaisesRegex(MODULE.TransactionError, message):
                    MODULE.build_transaction(
                        before_fact=before,
                        evidence=evidence,
                        transition=transition,
                        event=event,
                        source_is_authoritative=False,
                    )

    def test_fact_type_and_event_chain_mutations_reject(self):
        before, evidence, transition, event = self.inputs()
        evidence["result"]["canonical_type"] = "Wrong"
        with self.assertRaisesRegex(MODULE.TransactionError, "theorem type"):
            MODULE.build_transaction(
                before_fact=before,
                evidence=evidence,
                transition=transition,
                event=event,
                source_is_authoritative=False,
            )

        before, evidence, transition, event = self.inputs()
        event["identity"]["fact_id"] = "F:wrong"
        with self.assertRaisesRegex(MODULE.TransactionError, "bind"):
            MODULE.build_transaction(
                before_fact=before,
                evidence=evidence,
                transition=transition,
                event=event,
                source_is_authoritative=False,
            )

    def test_rehashed_proposal_cannot_claim_committed_admission(self):
        expected = self.build()
        mutated = copy.deepcopy(expected)
        mutated["state"] = "committed"
        mutated["admission_event"] = {"claimed": True}
        mutated["transaction_sha256"] = MODULE.digest(
            {key: value for key, value in mutated.items() if key != "transaction_sha256"}
        )
        with self.assertRaisesRegex(MODULE.TransactionError, "cannot claim"):
            MODULE.verify_transaction(mutated, expected)

    def test_fixture_operation_cannot_escalate_to_authoritative_write(self):
        before, evidence, transition, event = self.inputs()
        with self.assertRaisesRegex(MODULE.TransactionError, "counterfactual"):
            MODULE.build_transaction(
                before_fact=before,
                evidence=evidence,
                transition=transition,
                event=event,
                source_is_authoritative=True,
            )


class AuthoritativeFactTransactionTests(unittest.TestCase):
    def inputs(self):
        executor = MODULE.load_module("executor_for_transaction_test", MODULE.EXECUTOR_SCRIPT)
        frontier_module = executor.load_module("frontier_for_transaction_test", executor.FRONTIER_SCRIPT)
        facts = frontier_module.load()
        settle_reflexivity_fact(facts)
        target = copy.deepcopy(facts["F:no-integer-square-is-minus-one"])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        facts[target["id"]] = target
        frontier = frontier_module.build_machine_frontier(facts)
        before, operation, registry = executor.selected_inputs(frontier, facts)
        observation = {
            "verdict": "unsat",
            "evidence_label": "unsat-int-quadratic-negative-discriminant",
            "certified": True,
            "recheck": "na",
            "arena": "ok",
        }
        execution = executor.build_receipt(
            frontier=frontier,
            fact=before,
            operation=operation,
            registry=registry,
            git_commit="a" * 40,
            observation=observation,
        )
        return before, execution, operation, registry, observation

    def test_real_delta_is_derived_entirely_from_registered_execution(self):
        before, execution, operation, registry, observation = self.inputs()
        transaction = MODULE.build_authoritative_transaction(
            before_fact=before,
            execution=execution,
            operation=operation,
            registry=registry,
        )
        after = transaction["authoritative_write"]["after_fact"]
        self.assertTrue(transaction["precondition"]["source_is_authoritative"])
        self.assertEqual(after["proof_route"], "smt-term-level")
        self.assertEqual(after["axiom_footprint"], operation["admission"]["axiom_footprint"])
        self.assertNotEqual(after["axiom_footprint"], [])
        row = after["evidence"][0]
        self.assertEqual(row["kind"], "unsat-certificate")
        self.assertEqual(
            row["checker_command"],
            "python3 scripts/check-autogenesis-fact-operation.py --fact "
            "artifacts/facts/F-no-integer-square-is-minus-one.json",
        )
        checker = MODULE.load_module("fact_checker_for_transaction_test", MODULE.FACT_OPERATION_SCRIPT)
        checked = checker.check_fact(after, lambda _operation: observation)
        self.assertEqual(checked["operation_id"], operation["id"])
        self.assertTrue(after["notes"].startswith("CLOSED BY AXEYUM AUTOGENESIS"))
        self.assertIn("PRE-CLOSURE RECORD", after["notes"])

    def test_execution_identity_and_assurance_mutations_reject(self):
        before, execution, operation, registry, _observation = self.inputs()
        for path, value, message in (
            (("identity", "fact_sha256"), "b" * 64, "does not bind"),
            (("result", "axiom_footprint"), ["invented"], "assurance"),
            (("acceptance", "source_bound"), False, "assurance"),
        ):
            with self.subTest(path=path):
                changed = copy.deepcopy(execution)
                changed[path[0]][path[1]] = value
                with self.assertRaisesRegex(MODULE.TransactionError, message):
                    MODULE.build_authoritative_transaction(
                        before_fact=before,
                        execution=changed,
                        operation=operation,
                        registry=registry,
                    )

    def test_authoritative_kernel_delta_remains_axiom_free_and_replayable(self):
        executor = MODULE.load_module(
            "executor_for_kernel_transaction_test", MODULE.EXECUTOR_SCRIPT
        )
        frontier_module = executor.load_module(
            "frontier_for_kernel_transaction_test", executor.FRONTIER_SCRIPT
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
        before, operation, registry = executor.selected_inputs(frontier, facts)
        observation = {
            "verdict": "proved",
            "evidence_label": "kernel-term-axiom-free",
            "canonical_type": executor.formal_type(before),
            "axiom_footprint": [],
            "retained_answer_dependencies": [],
            "attempted": 2,
            "accepted_plan_rank": 2,
        }
        execution_receipt = executor.build_receipt(
            frontier=frontier,
            fact=before,
            operation=operation,
            registry=registry,
            git_commit="c" * 40,
            observation=observation,
        )
        transaction = MODULE.build_authoritative_transaction(
            before_fact=before,
            execution=execution_receipt,
            operation=operation,
            registry=registry,
        )
        after = transaction["authoritative_write"]["after_fact"]
        self.assertEqual(after["proof_route"], "kernel-lean")
        self.assertEqual(after["axiom_footprint"], [])
        binding = after["evidence"][0]["checker_operation"]
        self.assertEqual(binding["target_theorem"], "Nat.zero_add")
        self.assertNotIn("input_artifact", binding)
        checker = MODULE.load_module(
            "fact_checker_for_kernel_transaction_test", MODULE.FACT_OPERATION_SCRIPT
        )
        checked = checker.check_fact(after, lambda _operation: observation)
        self.assertEqual(checked["operation_id"], operation["id"])

    def test_episode_local_apply_delta_retains_trigger_chain(self):
        executor = MODULE.load_module(
            "executor_for_apply_transaction_test", MODULE.EXECUTOR_SCRIPT
        )
        frontier_module = executor.load_module(
            "frontier_for_apply_transaction_test", executor.FRONTIER_SCRIPT
        )
        facts = frontier_module.load()
        settle_reflexivity_fact(facts)
        target = copy.deepcopy(facts["F:nat-mul-one"])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        facts[target["id"]] = target
        frontier = frontier_module.build_machine_frontier(facts)
        before, operation, registry = executor.selected_inputs(frontier, facts)
        trigger = {
            "premise_fact_id": "F:nat-zero-add",
            "premise_operation_id": "authoritative-kernel-nat-zero-add-induction-v1",
            "premise_source_commit": "0" * 40,
            "premise_before_fact_sha256": "1" * 64,
            "premise_after_fact_sha256": "2" * 64,
            "premise_execution_sha256": "3" * 64,
            "premise_transaction_sha256": "4" * 64,
            "premise_admission_event_sha256": "5" * 64,
            "readiness_delta_sha256": "6" * 64,
            "frontier_after_sha256": frontier["frontier_sha256"],
        }
        observation = {
            "verdict": "proved",
            "evidence_label": operation["executor"]["expected_evidence_label"],
            "canonical_type": executor.formal_type(before),
            "axiom_footprint": [],
            "retained_answer_dependencies": [],
            "episode_dependency": "Autogenesis.Authoritative.E1111111111111111.premise",
            "attempted": 1,
            "accepted_plan_rank": 1,
            "premise_attempted": 2,
            "premise_plan_rank": 2,
        }
        receipt = executor.build_receipt(
            frontier=frontier,
            fact=before,
            operation=operation,
            registry=registry,
            git_commit="f" * 40,
            observation=observation,
            trigger=trigger,
        )
        transaction = MODULE.build_authoritative_transaction(
            before_fact=before,
            execution=receipt,
            operation=operation,
            registry=registry,
        )
        after = transaction["authoritative_write"]["after_fact"]
        binding = after["evidence"][0]["checker_operation"]
        self.assertEqual(binding["trigger"], trigger)
        self.assertEqual(binding["premise_fact_id"], "F:nat-zero-add")
        checker = MODULE.load_module(
            "fact_checker_for_apply_transaction_test", MODULE.FACT_OPERATION_SCRIPT
        )
        checked = checker.check_fact(
            after, lambda _operation, _trigger: observation
        )
        self.assertEqual(checked["operation_id"], operation["id"])

    def test_statement_reflexivity_delta_retains_external_and_proof_identities(self):
        executor = MODULE.load_module(
            "executor_for_reflexivity_transaction_test", MODULE.EXECUTOR_SCRIPT
        )
        frontier_module = executor.load_module(
            "frontier_for_reflexivity_transaction_test", executor.FRONTIER_SCRIPT
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
        before, operation, registry = executor.selected_inputs(frontier, facts)
        observation = executor.expected_statement_reflexivity_observation(
            operation, before
        )
        execution_receipt = executor.build_receipt(
            frontier=frontier,
            fact=before,
            operation=operation,
            registry=registry,
            git_commit="9" * 40,
            observation=observation,
        )
        transaction = MODULE.build_authoritative_transaction(
            before_fact=before,
            execution=execution_receipt,
            operation=operation,
            registry=registry,
        )
        after = transaction["authoritative_write"]["after_fact"]
        self.assertEqual(after["proof_route"], "kernel-lean")
        self.assertEqual(after["axiom_footprint"], [])
        binding = after["evidence"][0]["checker_operation"]
        self.assertEqual(binding["proof_sha256"], observation["proof_sha256"])
        self.assertEqual(
            binding["external_artifact_sha256"],
            observation["external_artifact_sha256"],
        )
        checker = MODULE.load_module(
            "fact_checker_for_reflexivity_transaction_test",
            MODULE.FACT_OPERATION_SCRIPT,
        )
        checked = checker.check_fact(after, lambda _operation: observation)
        self.assertEqual(checked["operation_id"], operation["id"])

    def test_checked_theorem_receipt_delta_retains_source_and_proof_identities(self):
        executor = MODULE.load_module(
            "executor_for_checked_theorem_transaction_test", MODULE.EXECUTOR_SCRIPT
        )
        frontier_module = executor.load_module(
            "frontier_for_checked_theorem_transaction_test", executor.FRONTIER_SCRIPT
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
        before, operation, registry = executor.selected_inputs(frontier, facts)
        self.assertEqual(before["id"], FIB_FACT)
        observation = executor.expected_checked_theorem_receipt_observation(
            operation, before
        )
        execution_receipt = executor.build_receipt(
            frontier=frontier,
            fact=before,
            operation=operation,
            registry=registry,
            git_commit="2" * 40,
            observation=observation,
        )
        transaction = MODULE.build_authoritative_transaction(
            before_fact=before,
            execution=execution_receipt,
            operation=operation,
            registry=registry,
        )
        after = transaction["authoritative_write"]["after_fact"]
        binding = after["evidence"][0]["checker_operation"]
        self.assertEqual(binding["receipt_sha256"], observation["receipt_sha256"])
        self.assertEqual(
            binding["source_artifact_sha256"],
            observation["source_artifact_sha256"],
        )
        checker = MODULE.load_module(
            "fact_checker_for_checked_theorem_transaction_test",
            MODULE.FACT_OPERATION_SCRIPT,
        )
        checked = checker.check_fact(after, lambda _operation: observation)
        self.assertEqual(checked["operation_id"], operation["id"])

    def test_dependency_receipt_delta_retains_exact_premise_identities(self):
        executor = MODULE.load_module(
            "executor_for_dependency_receipt_transaction_test",
            MODULE.EXECUTOR_SCRIPT,
        )
        frontier_module = executor.load_module(
            "frontier_for_dependency_receipt_transaction_test",
            executor.FRONTIER_SCRIPT,
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
        before, operation, registry = executor.selected_inputs(frontier, facts)
        self.assertEqual(before["id"], FIB_COPRIME_FACT)
        observation = executor.expected_dependency_theorem_receipt_observation(
            operation, before
        )
        execution_receipt = executor.build_receipt(
            frontier=frontier,
            fact=before,
            operation=operation,
            registry=registry,
            git_commit="4" * 40,
            observation=observation,
        )
        transaction = MODULE.build_authoritative_transaction(
            before_fact=before,
            execution=execution_receipt,
            operation=operation,
            registry=registry,
        )
        after = transaction["authoritative_write"]["after_fact"]
        binding = after["evidence"][0]["checker_operation"]
        self.assertEqual(len(binding["direct_theorem_dependencies"]), 8)
        self.assertEqual(binding["transitive_theorem_dependencies"], 115)
        checker = MODULE.load_module(
            "fact_checker_for_dependency_receipt_transaction_test",
            MODULE.FACT_OPERATION_SCRIPT,
        )
        checked = checker.check_fact(after, lambda _operation: observation)
        self.assertEqual(checked["operation_id"], operation["id"])

        changed = copy.deepcopy(execution_receipt)
        changed["result"]["observation"]["retained_answer_dependencies"] = []
        with self.assertRaisesRegex(MODULE.TransactionError, "assurance"):
            MODULE.build_authoritative_transaction(
                before_fact=before,
                execution=changed,
                operation=operation,
                registry=registry,
            )

    def test_zero_dependency_integer_fibonacci_capsule_is_admissible(self):
        executor = MODULE.load_module(
            "executor_for_int_fib_natcast_transaction_test",
            MODULE.EXECUTOR_SCRIPT,
        )
        frontier_module = executor.load_module(
            "frontier_for_int_fib_natcast_transaction_test",
            executor.FRONTIER_SCRIPT,
        )
        facts = frontier_module.load()
        settle_reflexivity_fact(facts)
        target = copy.deepcopy(facts[INT_FIB_NATCAST_FACT])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        facts[INT_FIB_NATCAST_FACT] = target
        frontier = frontier_module.build_machine_frontier(facts)
        before, operation, registry = executor.selected_inputs(frontier, facts)
        observation = executor.expected_sealed_kernel_capsule_observation(
            operation, before
        )
        self.assertEqual(observation["retained_answer_dependencies"], [])
        execution_receipt = executor.build_receipt(
            frontier={"frontier_sha256": "3" * 64},
            fact=before,
            operation=operation,
            registry=registry,
            git_commit="5" * 40,
            observation=observation,
        )
        transaction = MODULE.build_authoritative_transaction(
            before_fact=before,
            execution=execution_receipt,
            operation=operation,
            registry=registry,
        )
        binding = transaction["authoritative_write"]["after_fact"]["evidence"][0][
            "checker_operation"
        ]
        self.assertEqual(binding["direct_theorem_dependencies"], [])

        changed = copy.deepcopy(execution_receipt)
        changed["result"]["observation"]["fresh_imports"] = 4
        with self.assertRaisesRegex(MODULE.TransactionError, "assurance"):
            MODULE.build_authoritative_transaction(
                before_fact=before,
                execution=changed,
                operation=operation,
                registry=registry,
            )

    def test_three_dependency_integer_fibonacci_corollary_is_admissible(self):
        executor = MODULE.load_module(
            "executor_for_int_fib_corollary_transaction_test",
            MODULE.EXECUTOR_SCRIPT,
        )
        frontier_module = executor.load_module(
            "frontier_for_int_fib_corollary_transaction_test",
            executor.FRONTIER_SCRIPT,
        )
        facts = frontier_module.load()
        settle_reflexivity_fact(facts)
        target = copy.deepcopy(facts[INT_FIB_COROLLARY_FACT])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        facts[INT_FIB_COROLLARY_FACT] = target
        frontier = frontier_module.build_machine_frontier(facts)
        before, operation, registry = executor.selected_inputs(frontier, facts)
        self.assertEqual(before["id"], INT_FIB_COROLLARY_FACT)
        observation = executor.expected_sealed_kernel_capsule_observation(
            operation, before
        )
        self.assertEqual(
            observation["retained_answer_dependencies"],
            [
                "Axeyum.Autogenesis.intFibEqAddTwoSubAddOneResidualV2",
                "Int.add_neg_cancel_right",
                "Int.fib_add_two",
            ],
        )
        execution_receipt = executor.build_receipt(
            frontier={"frontier_sha256": "6" * 64},
            fact=before,
            operation=operation,
            registry=registry,
            git_commit="7" * 40,
            observation=observation,
        )
        transaction = MODULE.build_authoritative_transaction(
            before_fact=before,
            execution=execution_receipt,
            operation=operation,
            registry=registry,
        )
        binding = transaction["authoritative_write"]["after_fact"]["evidence"][0][
            "checker_operation"
        ]
        self.assertEqual(
            binding["direct_theorem_dependencies"],
            observation["retained_answer_dependencies"],
        )

        changed = copy.deepcopy(execution_receipt)
        changed["result"]["observation"]["fresh_imports"] = 4
        with self.assertRaisesRegex(MODULE.TransactionError, "assurance"):
            MODULE.build_authoritative_transaction(
                before_fact=before,
                execution=changed,
                operation=operation,
                registry=registry,
            )


if __name__ == "__main__":
    unittest.main()
