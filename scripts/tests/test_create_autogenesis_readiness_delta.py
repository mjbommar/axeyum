from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


READINESS_SCRIPT = pathlib.Path(__file__).parents[1] / "create-autogenesis-readiness-delta.py"
APPLY_SCRIPT = pathlib.Path(__file__).parents[1] / "apply-autogenesis-fact-transaction.py"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


MODULE = load("create_autogenesis_readiness_delta", READINESS_SCRIPT)
APPLY = load("apply_autogenesis_transaction_for_readiness_test", APPLY_SCRIPT)


class ReadinessDeltaTests(unittest.TestCase):
    def inputs(self):
        snapshot = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-counterfactual",
            "episode_id": "episode",
            "chain": {
                "premise": {"fact_id": "F:B"},
                "consequent": {"fact_id": "F:A"},
            },
            "withheld": {"fact_ids": ["F:A", "F:B"]},
            "phases": {"pre_a": {"visible_fact_ids": ["F:C"]}},
        }
        snapshot["snapshot_sha256"] = MODULE.digest(snapshot)
        transaction = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-fact-transaction-proposal",
            "state": "prepared",
            "identity": {
                "fact_id": "F:B",
                "episode_id": "episode",
                "before_fact_sha256": "before",
                "after_fact_sha256": "after",
                "premise_evidence_sha256": "evidence",
            },
            "precondition": {"source_is_authoritative": False},
            "authoritative_write": {
                "path": "artifacts/facts/F-B.json",
                "after_fact": {"epistemic_status": "proved"},
            },
            "admission_event": None,
        }
        transaction["transaction_sha256"] = MODULE.digest(transaction)
        event = APPLY.build_admission_event(transaction)
        facts = {
            "F:A": {"epistemic_status": "proved", "depends_on": ["F:B"]},
            "F:B": {"epistemic_status": "proved", "depends_on": []},
            "F:C": {"epistemic_status": "proved", "depends_on": []},
        }
        return snapshot, transaction, event, facts

    def build(self):
        snapshot, transaction, event, facts = self.inputs()
        return MODULE.build_delta(
            snapshot=snapshot,
            transaction=transaction,
            admission_event=event,
            facts=facts,
        )

    def test_durable_event_makes_exactly_a_ready(self):
        delta = self.build()
        self.assertEqual(delta["newly_ready"], ["F:A"])
        self.assertEqual(delta["target"]["before"]["missing_dependencies"], ["F:B"])
        self.assertTrue(delta["target"]["after"]["eligible"])
        self.assertEqual(delta["authoritative_ledger_writes"], 0)

    def test_wrong_event_and_missing_dependency_edge_reject(self):
        snapshot, transaction, event, facts = self.inputs()
        event["identity"]["fact_id"] = "F:wrong"
        event["event_sha256"] = APPLY.digest(
            {key: value for key, value in event.items() if key != "event_sha256"}
        )
        with self.assertRaisesRegex(MODULE.ReadinessError, "does not match"):
            MODULE.build_delta(
                snapshot=snapshot,
                transaction=transaction,
                admission_event=event,
                facts=facts,
            )

        snapshot, transaction, event, facts = self.inputs()
        facts["F:A"]["depends_on"] = []
        with self.assertRaisesRegex(MODULE.ReadinessError, "not a ledger dependency"):
            MODULE.build_delta(
                snapshot=snapshot,
                transaction=transaction,
                admission_event=event,
                facts=facts,
            )

    def test_rehashed_extra_newly_ready_fact_rejects(self):
        expected = self.build()
        mutated = copy.deepcopy(expected)
        mutated["newly_ready"].append("F:wrong")
        mutated["readiness_delta_sha256"] = MODULE.digest(
            {key: value for key, value in mutated.items() if key != "readiness_delta_sha256"}
        )
        with self.assertRaisesRegex(MODULE.ReadinessError, "wrong newly-ready"):
            MODULE.verify_delta(mutated, expected)


if __name__ == "__main__":
    unittest.main()
