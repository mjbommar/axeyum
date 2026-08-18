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


if __name__ == "__main__":
    unittest.main()
