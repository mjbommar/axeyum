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


if __name__ == "__main__":
    unittest.main()
