from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


EVENT_SCRIPT = pathlib.Path(__file__).parents[1] / "create-autogenesis-accepted-event.py"
TRANSITION_SCRIPT = (
    pathlib.Path(__file__).parents[1] / "create-autogenesis-premise-transition.py"
)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


MODULE = load("create_autogenesis_accepted_event", EVENT_SCRIPT)
TRANSITION = load("create_autogenesis_premise_transition_for_event_test", TRANSITION_SCRIPT)


class AcceptedEventTests(unittest.TestCase):
    def inputs(self):
        declaration = "Autogenesis.Episode.premise"
        denied = ["Nat.mul_one", "Nat.zero_add"]
        snapshot = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-counterfactual",
            "episode_id": "episode",
            "identity": {
                "facts": {
                    "premise": {"id": "F:nat-zero-add", "sha256": "fact-sha"}
                }
            },
            "chain": {"premise": {"fact_id": "F:nat-zero-add"}},
            "withheld": {"retained_theorems": denied},
            "phases": {
                "pre_b": {
                    "target_candidate": declaration,
                    "denied_theorems": denied,
                    "visible_retained_theorems": ["Nat.add_zero"],
                },
                "post_b": {
                    "accepted_episode_facts": [
                        {
                            "declaration": declaration,
                            "role": "premise",
                            "source_fact_id": "F:nat-zero-add",
                        }
                    ],
                    "required_dependencies": [declaration],
                    "denied_theorems": denied,
                    "visible_retained_theorems": ["Nat.add_zero"],
                },
            },
        }
        snapshot["snapshot_sha256"] = TRANSITION.digest(snapshot)
        evidence = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-kernel-premise-evidence",
            "identity": {
                "episode_id": "episode",
                "snapshot_sha256": snapshot["snapshot_sha256"],
                "fact_id": "F:nat-zero-add",
            },
            "result": {"outcome": "proved", "declaration": declaration},
            "acceptance": {
                "independent_kernel_checked": True,
                "axiom_footprint": [],
                "retained_answer_dependencies": [],
            },
        }
        evidence["evidence_sha256"] = TRANSITION.digest(evidence)
        transition = TRANSITION.build_transition(snapshot=snapshot, evidence=evidence)
        return snapshot, evidence, transition

    def test_event_binds_checked_transition_and_has_no_ledger_write(self):
        snapshot, evidence, transition = self.inputs()
        event = MODULE.build_event(
            snapshot=snapshot, evidence=evidence, transition=transition
        )
        unsigned = dict(event)
        unsigned.pop("event_sha256")
        self.assertEqual(event["event_sha256"], MODULE.digest(unsigned))
        self.assertEqual(event["identity"]["transition_sha256"], transition["transition_sha256"])
        self.assertEqual(event["authoritative_ledger_writes"], [])

    def test_mutated_transition_cannot_emit_event(self):
        snapshot, evidence, transition = self.inputs()
        transition["after"]["accepted_episode_facts"][0]["source_fact_id"] = "F:wrong"
        transition["transition_sha256"] = TRANSITION.digest(
            {key: value for key, value in transition.items() if key != "transition_sha256"}
        )
        with self.assertRaisesRegex(MODULE.EventError, "transition verification"):
            MODULE.build_event(
                snapshot=snapshot, evidence=evidence, transition=transition
            )

    def test_replay_rejects_rehashed_ledger_write(self):
        snapshot, evidence, transition = self.inputs()
        expected = MODULE.build_event(
            snapshot=snapshot, evidence=evidence, transition=transition
        )
        mutated = copy.deepcopy(expected)
        mutated["authoritative_ledger_writes"] = [{"path": "artifacts/facts/B.json"}]
        mutated["event_sha256"] = MODULE.digest(
            {key: value for key, value in mutated.items() if key != "event_sha256"}
        )
        with self.assertRaisesRegex(MODULE.EventError, "zero ledger writes"):
            MODULE.verify_event(mutated, expected)


if __name__ == "__main__":
    unittest.main()
