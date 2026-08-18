from __future__ import annotations

import importlib.util
import pathlib
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "create-autogenesis-proposer-catalog.py"
SPEC = importlib.util.spec_from_file_location("create_autogenesis_proposer_catalog", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class CatalogTests(unittest.TestCase):
    def inputs(self, phase: str):
        snapshot = {
            "episode_id": "episode",
            "snapshot_sha256": "snapshot",
            "chain": {
                "premise": {"fact_id": "F:B", "retained_theorem": "Nat.B"},
                "consequent": {"fact_id": "F:A", "retained_theorem": "Nat.A"},
            },
            "phases": {
                "pre_b": {
                    "visible_retained_theorems": ["Nat.C"],
                    "denied_theorems": ["Nat.A", "Nat.B"],
                    "target_candidate": "Autogenesis.E.premise",
                },
                "pre_a": {
                    "visible_retained_theorems": ["Nat.C"],
                    "denied_theorems": ["Nat.A", "Nat.B"],
                    "target_candidate": "Autogenesis.E.consequent",
                },
                "post_b": {
                    "visible_retained_theorems": ["Nat.C"],
                    "denied_theorems": ["Nat.A", "Nat.B"],
                    "accepted_episode_facts": [
                        {
                            "declaration": "Autogenesis.E.premise",
                            "source_fact_id": "F:B",
                        }
                    ],
                    "target_candidate": "Autogenesis.E.consequent",
                },
            },
        }
        facts = {
            "F:B": {"id": "F:B", "formal": {"statement": "theorem Nat.B : BType"}},
            "F:A": {"id": "F:A", "formal": {"statement": "theorem Nat.A : AType"}},
        }
        inventory = {
            "Nat.A": {"arity": 1, "canonical_type": "AType"},
            "Nat.B": {"arity": 1, "canonical_type": "BType"},
            "Nat.C": {"arity": 0, "canonical_type": "CType"},
        }
        event = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-accepted-transition-event",
            "event_type": "episode-fact-accepted",
            "sequence": 1,
            "identity": {
                "episode_id": "episode",
                "snapshot_sha256": "snapshot",
                "fact_id": "F:B",
            },
            "state_change": {
                "from_phase": "pre_b",
                "to_phase": "post_b",
                "accepted_episode_facts": snapshot["phases"]["post_b"][
                    "accepted_episode_facts"
                ],
            },
            "authoritative_ledger_writes": [],
        }
        event["event_sha256"] = MODULE.digest(event)
        return dict(
            snapshot=snapshot,
            phase=phase,
            facts=facts,
            inventory=inventory,
            accepted_event=event if phase == "post_b" else None,
        )

    def test_pre_b_contains_types_but_no_proof_fields(self):
        catalog = MODULE.build_catalog(**self.inputs("pre_b"))
        self.assertFalse(catalog["proof_bodies_included"])
        self.assertEqual([entry["name"] for entry in catalog["entries"]], ["Nat.C"])
        self.assertEqual(catalog["entries"][0]["arity"], 0)
        MODULE.verify_catalog(catalog, catalog)

    def test_post_b_exposes_only_episode_local_premise(self):
        catalog = MODULE.build_catalog(**self.inputs("post_b"))
        names = [entry["name"] for entry in catalog["entries"]]
        self.assertIn("Autogenesis.E.premise", names)
        self.assertNotIn("Nat.B", names)
        self.assertEqual(catalog["target"]["name"], "Autogenesis.E.consequent")
        self.assertEqual(
            catalog["accepted_transition_event_sha256"],
            self.inputs("post_b")["accepted_event"]["event_sha256"],
        )

    def test_post_b_without_event_rejects(self):
        inputs = self.inputs("post_b")
        inputs["accepted_event"] = None
        with self.assertRaisesRegex(MODULE.CatalogError, "requires"):
            MODULE.build_catalog(**inputs)

    def test_rehashed_event_for_wrong_fact_rejects(self):
        inputs = self.inputs("post_b")
        event = inputs["accepted_event"]
        event["identity"]["fact_id"] = "F:wrong"
        event["event_sha256"] = MODULE.digest(
            {key: value for key, value in event.items() if key != "event_sha256"}
        )
        with self.assertRaisesRegex(MODULE.CatalogError, "identity"):
            MODULE.build_catalog(**inputs)

    def test_pre_a_has_same_target_as_post_b_without_episode_premise(self):
        pre = MODULE.build_catalog(**self.inputs("pre_a"))
        post = MODULE.build_catalog(**self.inputs("post_b"))
        self.assertEqual(pre["target"], post["target"])
        self.assertNotIn("Autogenesis.E.premise", {entry["name"] for entry in pre["entries"]})

    def test_mutation_of_type_or_digest_rejects(self):
        catalog = MODULE.build_catalog(**self.inputs("post_b"))
        expected = MODULE.build_catalog(**self.inputs("post_b"))
        catalog["entries"][0]["canonical_type"] = "mutated"
        with self.assertRaisesRegex(MODULE.CatalogError, "catalog_sha256"):
            MODULE.verify_catalog(catalog, expected)

    def test_proof_bearing_entry_rejects_even_with_rehashed_catalog(self):
        catalog = MODULE.build_catalog(**self.inputs("post_b"))
        catalog["entries"][0]["proof_body"] = "secret"
        catalog["catalog_sha256"] = MODULE.digest(
            {key: value for key, value in catalog.items() if key != "catalog_sha256"}
        )
        with self.assertRaisesRegex(MODULE.CatalogError, "proof-bearing keys"):
            MODULE.verify_catalog(catalog, MODULE.build_catalog(**self.inputs("post_b")))

    def test_ledger_statement_type_mismatch_rejects(self):
        inputs = self.inputs("pre_b")
        inputs["facts"]["F:B"]["formal"]["statement"] = "theorem Nat.B : Wrong"
        with self.assertRaisesRegex(MODULE.CatalogError, "disagrees"):
            MODULE.build_catalog(**inputs)

    def test_malformed_entries_fail_as_catalog_error(self):
        expected = MODULE.build_catalog(**self.inputs("pre_b"))
        malformed = dict(expected)
        malformed["entries"] = "not-a-list"
        malformed["catalog_sha256"] = MODULE.digest(
            {key: value for key, value in malformed.items() if key != "catalog_sha256"}
        )
        with self.assertRaisesRegex(MODULE.CatalogError, "must be a list"):
            MODULE.verify_catalog(malformed, expected)


if __name__ == "__main__":
    unittest.main()
