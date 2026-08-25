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

    def test_authoritative_frontier_change_can_honestly_unlock_nothing(self):
        before = {"selection": {"ready_fact_ids": ["F:B"], "selected_fact_id": "F:B"}}
        after = {"selection": {"ready_fact_ids": [], "selected_fact_id": None}}
        newly, removed = MODULE.frontier_change(before, after, "F:B")
        self.assertEqual(newly, [])
        self.assertEqual(removed, ["F:B"])

    def test_authoritative_frontier_change_reports_a_real_unlock(self):
        before = {"selection": {"ready_fact_ids": ["F:B"], "selected_fact_id": "F:B"}}
        after = {"selection": {"ready_fact_ids": ["F:A"], "selected_fact_id": None}}
        newly, removed = MODULE.frontier_change(before, after, "F:B")
        self.assertEqual(newly, ["F:A"])
        self.assertEqual(removed, ["F:B"])

    def test_authoritative_frontier_change_rejects_unrelated_disappearance(self):
        before = {
            "selection": {
                "ready_fact_ids": ["F:B", "F:unrelated"],
                "selected_fact_id": "F:B",
            }
        }
        after = {"selection": {"ready_fact_ids": [], "selected_fact_id": None}}
        with self.assertRaisesRegex(MODULE.ReadinessError, "beyond"):
            MODULE.frontier_change(before, after, "F:B")

    def authoritative_inputs(self):
        frontier = MODULE.load_frontier_module()
        registry = frontier.load_operation_registry()
        facts = frontier.load()
        # `authoritative-mathlib-modeq-family-v1` (registered 2026-08-25 as
        # `authoritative-mathlib-nat-modeq-family-v1`, merged the same day
        # into the Int.ModEq operation under this id) makes both of these
        # `open` and dependency-ready on the LIVE ledger, and they sort
        # lexicographically ahead of `admitted` below (`F:ml430-...` <
        # `F:no-integer...`). Left unneutralized, the "before" frontier
        # selects one of these instead of `admitted`, and this test's whole
        # point is that the "before" frontier selects `admitted`.
        for fact_id in (
            "F:ml430-nat-modeq-symm-0a3d4d18",
            "F:ml430-nat-modeq-trans-ef9d1c46",
        ):
            facts[fact_id] = copy.deepcopy(facts[fact_id])
            facts[fact_id]["epistemic_status"] = "proved"
        admitted = "F:no-integer-square-is-minus-one"
        before_facts = copy.deepcopy(facts)
        before = before_facts[admitted]
        before["epistemic_status"] = "open"
        before["evidence"] = []
        before.pop("proof_route", None)
        before.pop("axiom_footprint", None)
        execution = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-operation-execution",
            "identity": {
                "fact_id": admitted,
                "fact_sha256": MODULE.digest(before),
                "operation_registry_sha256": MODULE.digest(registry),
            },
        }
        execution["execution_sha256"] = MODULE.digest(execution)
        transaction = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-fact-transaction-proposal",
            "state": "prepared",
            "identity": {
                "fact_id": admitted,
                "episode_id": "episode",
                "execution_sha256": execution["execution_sha256"],
                "before_fact_sha256": MODULE.digest(before),
                "after_fact_sha256": MODULE.digest(facts[admitted]),
                "premise_evidence_sha256": execution["execution_sha256"],
            },
            "precondition": {"source_is_authoritative": True},
            "authoritative_write": {"after_fact": facts[admitted]},
            "admission_event": None,
        }
        transaction["transaction_sha256"] = MODULE.digest(transaction)
        event = APPLY.build_admission_event(transaction)
        return {
            "transaction": transaction,
            "admission_event": event,
            "execution": execution,
            "frontier_before": frontier.build_machine_frontier(before_facts, registry),
            "frontier_after": frontier.build_machine_frontier(facts, registry),
            "before_facts": before_facts,
            "facts": facts,
            "registry": registry,
        }

    def test_authoritative_delta_binds_only_the_admitted_ledger_change(self):
        inputs = self.authoritative_inputs()
        delta = MODULE.build_authoritative_delta(**inputs)
        self.assertEqual(delta["newly_ready"], [])
        self.assertEqual(delta["frontier_change"]["no_longer_ready"], [
            "F:no-integer-square-is-minus-one"
        ])
        self.assertEqual(delta["authoritative_ledger_writes"], 1)

        inputs["before_facts"]["F:bool-and-comm"] = copy.deepcopy(
            inputs["facts"]["F:bool-and-comm"]
        )
        inputs["before_facts"]["F:bool-and-comm"]["title"] += " mutated"
        with self.assertRaisesRegex(MODULE.ReadinessError, "beyond"):
            MODULE.build_authoritative_delta(**inputs)


if __name__ == "__main__":
    unittest.main()
