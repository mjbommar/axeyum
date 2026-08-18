from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import tempfile
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "apply-autogenesis-fact-transaction.py"
SPEC = importlib.util.spec_from_file_location("apply_autogenesis_fact_transaction", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class FactTransactionApplyTests(unittest.TestCase):
    def transaction(self):
        before = {
            "id": "F:nat-zero-add",
            "epistemic_status": "open",
            "evidence": [],
        }
        after = {
            "id": "F:nat-zero-add",
            "epistemic_status": "proved",
            "evidence": [{"check_status": "checked"}],
        }
        transaction = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-fact-transaction-proposal",
            "state": "prepared",
            "identity": {
                "fact_id": "F:nat-zero-add",
                "episode_id": "episode",
                "before_fact_sha256": MODULE.digest(before),
                "after_fact_sha256": MODULE.digest(after),
                "premise_evidence_sha256": "evidence",
            },
            "precondition": {"source_is_authoritative": False},
            "authoritative_write": {
                "path": "artifacts/facts/F-nat-zero-add.json",
                "after_fact": after,
            },
            "admission_event": None,
        }
        transaction["transaction_sha256"] = MODULE.digest(transaction)
        return before, after, transaction

    def run_fault(self, fault):
        before, after, transaction = self.transaction()
        with tempfile.TemporaryDirectory() as raw:
            root = pathlib.Path(raw)
            facts = root / "facts"
            journal = root / "journal"
            facts.mkdir()
            target = facts / "F-nat-zero-add.json"
            target.write_text(json.dumps(before))
            with self.assertRaises(MODULE.InjectedFault):
                MODULE.apply_or_recover(
                    transaction=transaction,
                    target=target,
                    journal_root=journal,
                    fault_after=fault,
                )
            event = MODULE.apply_or_recover(
                transaction=transaction,
                target=target,
                journal_root=journal,
            )
            self.assertEqual(json.loads(target.read_text()), after)
            event_path = journal / transaction["transaction_sha256"] / "admission-event.json"
            self.assertEqual(json.loads(event_path.read_text()), event)
            return event

    def test_fault_boundaries_recover_to_identical_event(self):
        events = [self.run_fault(fault) for fault in ("intent", "fact", "event")]
        self.assertEqual(events[0], events[1])
        self.assertEqual(events[1], events[2])

    def test_compare_and_swap_rejects_unknown_fact_state(self):
        before, _after, transaction = self.transaction()
        with tempfile.TemporaryDirectory() as raw:
            root = pathlib.Path(raw)
            facts = root / "facts"
            facts.mkdir()
            target = facts / "F-nat-zero-add.json"
            target.write_text(json.dumps({**before, "unexpected": True}))
            with self.assertRaisesRegex(MODULE.ApplyError, "compare-and-swap"):
                MODULE.apply_or_recover(
                    transaction=transaction,
                    target=target,
                    journal_root=root / "journal",
                )

    def test_committed_event_with_rolled_back_fact_is_corruption(self):
        before, _after, transaction = self.transaction()
        with tempfile.TemporaryDirectory() as raw:
            root = pathlib.Path(raw)
            facts = root / "facts"
            facts.mkdir()
            target = facts / "F-nat-zero-add.json"
            target.write_text(json.dumps(before))
            MODULE.apply_or_recover(
                transaction=transaction,
                target=target,
                journal_root=root / "journal",
            )
            target.write_text(json.dumps(before))
            with self.assertRaisesRegex(MODULE.ApplyError, "fact is not"):
                MODULE.apply_or_recover(
                    transaction=transaction,
                    target=target,
                    journal_root=root / "journal",
                )

    def test_production_authority_rejects_fixture_proposal(self):
        _before, _after, transaction = self.transaction()
        with self.assertRaisesRegex(MODULE.ApplyError, "non-authoritative"):
            MODULE.authorize_target(transaction, None)

    def test_rehashed_committed_proposal_is_not_applicable(self):
        _before, _after, transaction = self.transaction()
        mutated = copy.deepcopy(transaction)
        mutated["state"] = "committed"
        mutated["transaction_sha256"] = MODULE.digest(
            {key: value for key, value in mutated.items() if key != "transaction_sha256"}
        )
        with tempfile.TemporaryDirectory() as raw:
            root = pathlib.Path(raw)
            target = root / "F-nat-zero-add.json"
            target.write_text("{}")
            with self.assertRaisesRegex(MODULE.ApplyError, "prepared proposal"):
                MODULE.apply_or_recover(
                    transaction=mutated,
                    target=target,
                    journal_root=root / "journal",
                )

    def test_replay_free_recovery_requires_the_durable_intent(self):
        before, _after, transaction = self.transaction()
        with tempfile.TemporaryDirectory() as raw:
            root = pathlib.Path(raw)
            journal = root / "journal"
            with self.assertRaisesRegex(MODULE.ApplyError, "existing durable"):
                MODULE.require_recovery_intent(transaction, journal)

            target = root / "F-nat-zero-add.json"
            target.write_text(json.dumps(before))
            with self.assertRaises(MODULE.InjectedFault):
                MODULE.apply_or_recover(
                    transaction=transaction,
                    target=target,
                    journal_root=journal,
                    fault_after="intent",
                )
            intent = MODULE.require_recovery_intent(transaction, journal)
            self.assertTrue(intent.is_file())


if __name__ == "__main__":
    unittest.main()
