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


class AuthoritativeFactTransactionTests(unittest.TestCase):
    def inputs(self):
        executor = MODULE.load_module("executor_for_transaction_test", MODULE.EXECUTOR_SCRIPT)
        frontier_module = executor.load_module("frontier_for_transaction_test", executor.FRONTIER_SCRIPT)
        facts = frontier_module.load()
        frontier = frontier_module.build_machine_frontier(facts)
        before, operation, registry = executor.selected_inputs(frontier)
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


if __name__ == "__main__":
    unittest.main()
