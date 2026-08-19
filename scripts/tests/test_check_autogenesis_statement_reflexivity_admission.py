from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-statement-reflexivity-admission.py"
SPEC = importlib.util.spec_from_file_location(
    "check_autogenesis_statement_reflexivity_admission", SCRIPT
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def addressed(value, field):
    value[field] = MODULE.digest(value)
    return value


class StatementReflexivityAdmissionResultTests(unittest.TestCase):
    def inputs(self):
        fact_id = "F:ml430-nat-ascfactorial-zero-fd183202"
        operation_id = "authoritative-mathlib-statement-reflexivity-v1"
        before_fact = {"id": fact_id, "epistemic_status": "open", "evidence": []}
        after_fact = {
            "id": fact_id,
            "epistemic_status": "proved",
            "proof_route": "kernel-lean",
            "axiom_footprint": [],
            "evidence": [{}],
        }
        before = addressed(
            {"selection": {"selected_fact_id": fact_id}}, "frontier_sha256"
        )
        execution = addressed(
            {
                "identity": {
                    "git_commit": "a" * 40,
                    "fact_id": fact_id,
                    "operation_id": operation_id,
                },
                "result": {
                    "observation": {
                        "axiom_footprint": [],
                        "retained_answer_dependencies": [],
                        "target_dependency": False,
                    }
                },
            },
            "execution_sha256",
        )
        transaction = addressed(
            {
                "identity": {
                    "fact_id": fact_id,
                    "episode_id": "episode",
                    "before_fact_sha256": MODULE.digest(before_fact),
                    "after_fact_sha256": MODULE.digest(after_fact),
                    "premise_evidence_sha256": execution["execution_sha256"],
                    "execution_sha256": execution["execution_sha256"],
                },
                "authoritative_write": {"after_fact": after_fact},
            },
            "transaction_sha256",
        )
        apply = MODULE.load_module("apply_for_admission_result_test", MODULE.APPLY_SCRIPT)
        event = apply.build_admission_event(transaction)
        after = addressed(
            {"selection": {"selected_fact_id": None}}, "frontier_sha256"
        )
        readiness = addressed(
            {
                "identity": {
                    "transaction_sha256": transaction["transaction_sha256"],
                    "durable_admission_event_sha256": event["event_sha256"],
                },
                "authoritative_ledger_writes": 1,
                "fixture_writes": 0,
                "newly_ready": [],
                "frontier_change": {"no_longer_ready": [fact_id]},
            },
            "readiness_delta_sha256",
        )
        objects = {
            "frontier-before.json": before,
            "execution.json": execution,
            "transaction.json": transaction,
            "admission-event.json": event,
            "frontier-after.json": after,
            "readiness.json": readiness,
            "before-fact.json": before_fact,
            "after-fact.json": after_fact,
        }
        manifest = {
            "fact_id": fact_id,
            "operation_id": operation_id,
            "registration_commit": "a" * 40,
            "fault_injection": {
                "boundary": "after-intent",
                "exit_status": 75,
                "fact_unchanged_before_recovery": True,
            },
            "identities": {
                "frontier_before_sha256": before["frontier_sha256"],
                "execution_sha256": execution["execution_sha256"],
                "transaction_sha256": transaction["transaction_sha256"],
                "admission_event_sha256": event["event_sha256"],
                "frontier_after_sha256": after["frontier_sha256"],
                "readiness_delta_sha256": readiness["readiness_delta_sha256"],
                "before_fact_sha256": MODULE.digest(before_fact),
                "after_fact_sha256": MODULE.digest(after_fact),
            },
            "result": {
                "authoritative_ledger_writes": 1,
                "fixture_writes": 0,
                "newly_ready": [],
                "axiom_footprint": [],
                "theorem_dependencies": [],
                "target_dependency": False,
            },
        }
        return manifest, objects, after_fact

    def replay_inputs(self):
        manifest, objects, current = self.inputs()
        fresh = {
            name: copy.deepcopy(objects[name])
            for name in (
                "frontier-before.json",
                "execution.json",
                "transaction.json",
                "admission-event.json",
                "frontier-after.json",
                "readiness.json",
            )
        }
        checks = {
            "same_fact": True,
            "same_registered_operation": True,
            "same_certified_result": True,
            "same_acceptance_policy": True,
            "selected_before": True,
            "admitted_event": True,
            "removed_from_ready": True,
            "honest_leaf_unlock": True,
            "one_authoritative_write": True,
            "zero_fixture_writes": True,
        }
        report = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-authoritative-admission-replay",
            "mode": "isolated-clean-worktree-semantic-reproduction",
            "source_head": "b" * 40,
            "historical_prestate_commit": manifest["registration_commit"],
            "reconstructed_replay_commit": "c" * 40,
            "identity": {
                "fact_id": manifest["fact_id"],
                "operation_id": manifest["operation_id"],
            },
            "fault_injection": manifest["fault_injection"],
            "checks": checks,
            "retained": {
                "execution_sha256": manifest["identities"]["execution_sha256"],
                "transaction_sha256": manifest["identities"]["transaction_sha256"],
                "event_sha256": manifest["identities"]["admission_event_sha256"],
                "readiness_delta_sha256": manifest["identities"][
                    "readiness_delta_sha256"
                ],
            },
            "fresh": {
                "frontier_before_sha256": fresh["frontier-before.json"][
                    "frontier_sha256"
                ],
                "execution_sha256": fresh["execution.json"]["execution_sha256"],
                "transaction_sha256": fresh["transaction.json"][
                    "transaction_sha256"
                ],
                "event_sha256": fresh["admission-event.json"]["event_sha256"],
                "frontier_after_sha256": fresh["frontier-after.json"][
                    "frontier_sha256"
                ],
                "readiness_delta_sha256": fresh["readiness.json"][
                    "readiness_delta_sha256"
                ],
            },
        }
        addressed(report, "replay_sha256")
        manifest["clean_replay"] = {
            "source_commit": "b" * 40,
            "replay_sha256": report["replay_sha256"],
            "fresh_execution_sha256": report["fresh"]["execution_sha256"],
            "fresh_transaction_sha256": report["fresh"]["transaction_sha256"],
            "fresh_event_sha256": report["fresh"]["event_sha256"],
            "fresh_readiness_delta_sha256": report["fresh"][
                "readiness_delta_sha256"
            ],
        }
        return manifest, report, fresh, objects, current

    def test_exact_admission_chain_is_accepted(self):
        manifest, objects, current = self.inputs()
        MODULE.validate_objects(manifest, objects, current)

    def test_rehashed_event_mutation_is_rejected(self):
        manifest, objects, current = self.inputs()
        objects["admission-event.json"]["publication"]["git_published"] = True
        objects["admission-event.json"].pop("event_sha256")
        addressed(objects["admission-event.json"], "event_sha256")
        manifest["identities"]["admission_event_sha256"] = objects[
            "admission-event.json"
        ]["event_sha256"]
        readiness = objects["readiness.json"]
        readiness["identity"]["durable_admission_event_sha256"] = objects[
            "admission-event.json"
        ]["event_sha256"]
        readiness.pop("readiness_delta_sha256")
        addressed(readiness, "readiness_delta_sha256")
        manifest["identities"]["readiness_delta_sha256"] = readiness[
            "readiness_delta_sha256"
        ]
        with self.assertRaisesRegex(MODULE.AdmissionResultError, "does not derive"):
            MODULE.validate_objects(manifest, objects, current)

    def test_current_ledger_must_equal_transaction_after_state(self):
        manifest, objects, current = self.inputs()
        changed = copy.deepcopy(current)
        changed["proof_route"] = "smt-term-level"
        with self.assertRaisesRegex(MODULE.AdmissionResultError, "ledger differs"):
            MODULE.validate_objects(manifest, objects, changed)

    def test_exact_clean_replay_chain_is_accepted(self):
        manifest, report, fresh, retained, _current = self.replay_inputs()
        MODULE.validate_replay_objects(manifest, report, fresh, retained)

    def test_clean_replay_must_retain_every_semantic_check(self):
        manifest, report, fresh, retained, _current = self.replay_inputs()
        report["checks"]["same_certified_result"] = False
        report.pop("replay_sha256")
        addressed(report, "replay_sha256")
        manifest["clean_replay"]["replay_sha256"] = report["replay_sha256"]
        with self.assertRaisesRegex(MODULE.AdmissionResultError, "incomplete"):
            MODULE.validate_replay_objects(manifest, report, fresh, retained)


if __name__ == "__main__":
    unittest.main()
