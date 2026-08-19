from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "create-autogenesis-premise-transition.py"
SPEC = importlib.util.spec_from_file_location("create_autogenesis_premise_transition", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class PremiseTransitionTests(unittest.TestCase):
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
        snapshot["snapshot_sha256"] = MODULE.digest(snapshot)
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
        evidence["evidence_sha256"] = MODULE.digest(evidence)
        return snapshot, evidence

    def rebind_snapshot(self, snapshot, evidence):
        snapshot.pop("snapshot_sha256", None)
        snapshot["snapshot_sha256"] = MODULE.digest(snapshot)
        evidence["identity"]["snapshot_sha256"] = snapshot["snapshot_sha256"]
        evidence.pop("evidence_sha256", None)
        evidence["evidence_sha256"] = MODULE.digest(evidence)

    def test_transition_is_content_addressed_and_never_writes_ledger(self):
        snapshot, evidence = self.inputs()
        transition = MODULE.build_transition(snapshot=snapshot, evidence=evidence)
        unsigned = dict(transition)
        unsigned.pop("transition_sha256")
        self.assertEqual(transition["transition_sha256"], MODULE.digest(unsigned))
        self.assertEqual(transition["authoritative_ledger"]["writes"], [])
        self.assertFalse(transition["before"]["premise_available"])
        self.assertTrue(transition["after"]["premise_available"])

    def test_evidence_and_accepted_fact_mutations_reject(self):
        mutations = (
            ("result", "outcome", "unknown", "proved"),
            ("acceptance", "independent_kernel_checked", False, "kernel"),
            ("acceptance", "axiom_footprint", ["Classical.choice"], "axiom"),
            (
                "acceptance",
                "retained_answer_dependencies",
                ["Nat.zero_add"],
                "retained answer",
            ),
        )
        for section, key, value, message in mutations:
            with self.subTest(key=key):
                snapshot, evidence = self.inputs()
                evidence[section][key] = value
                evidence["evidence_sha256"] = MODULE.digest(
                    {k: v for k, v in evidence.items() if k != "evidence_sha256"}
                )
                with self.assertRaisesRegex(MODULE.TransitionError, message):
                    MODULE.build_transition(snapshot=snapshot, evidence=evidence)

        snapshot, evidence = self.inputs()
        snapshot["phases"]["post_b"]["accepted_episode_facts"][0][
            "source_fact_id"
        ] = "F:wrong"
        self.rebind_snapshot(snapshot, evidence)
        with self.assertRaisesRegex(MODULE.TransitionError, "accepted episode fact"):
            MODULE.build_transition(snapshot=snapshot, evidence=evidence)

    def test_stale_digest_and_answer_leakage_reject(self):
        snapshot, evidence = self.inputs()
        evidence["result"]["declaration"] = "mutated"
        with self.assertRaisesRegex(MODULE.TransitionError, "digest"):
            MODULE.build_transition(snapshot=snapshot, evidence=evidence)

        snapshot, evidence = self.inputs()
        snapshot["phases"]["post_b"]["visible_retained_theorems"].append(
            "Nat.zero_add"
        )
        self.rebind_snapshot(snapshot, evidence)
        with self.assertRaisesRegex(MODULE.TransitionError, "exposes"):
            MODULE.build_transition(snapshot=snapshot, evidence=evidence)

    def test_replay_rejects_authoritative_ledger_write_even_if_rehashed(self):
        snapshot, evidence = self.inputs()
        expected = MODULE.build_transition(snapshot=snapshot, evidence=evidence)
        mutated = copy.deepcopy(expected)
        mutated["authoritative_ledger"]["writes"] = [
            {"path": "artifacts/facts/nat-zero-add.json"}
        ]
        mutated["transition_sha256"] = MODULE.digest(
            {key: value for key, value in mutated.items() if key != "transition_sha256"}
        )
        with self.assertRaisesRegex(MODULE.TransitionError, "zero ledger writes"):
            MODULE.verify_transition(mutated, expected)

    def test_preexisting_episode_fact_and_denied_set_drift_reject(self):
        snapshot, evidence = self.inputs()
        snapshot["phases"]["pre_b"]["accepted_episode_facts"] = [{}]
        self.rebind_snapshot(snapshot, evidence)
        with self.assertRaisesRegex(MODULE.TransitionError, "already contains"):
            MODULE.build_transition(snapshot=snapshot, evidence=evidence)

        snapshot, evidence = self.inputs()
        snapshot["phases"]["post_b"]["denied_theorems"] = ["Nat.zero_add"]
        self.rebind_snapshot(snapshot, evidence)
        with self.assertRaisesRegex(MODULE.TransitionError, "drifted"):
            MODULE.build_transition(snapshot=snapshot, evidence=evidence)


if __name__ == "__main__":
    unittest.main()
