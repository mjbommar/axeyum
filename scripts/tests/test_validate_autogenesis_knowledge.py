import copy
import importlib.util
import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "validate_autogenesis_knowledge",
    ROOT / "scripts/validate-autogenesis-knowledge.py",
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ValidateAutogenesisKnowledgeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.doc = json.loads(
            (ROOT / "artifacts/autogenesis/knowledge-overlay-v1.json").read_text()
        )

    def errors_for(self, doc):
        errors, _warnings = MODULE.validate_document(doc, ROOT)
        return errors

    def test_committed_overlay_passes(self):
        self.assertEqual(self.errors_for(self.doc), [])

    def test_unknown_local_fact_fails(self):
        doc = copy.deepcopy(self.doc)
        doc["links"][0]["source"] = {
            "namespace": "axeyum-fact",
            "kind": "fact",
            "id": "F:not-a-real-fact",
        }
        self.assertTrue(any("unknown fact" in error for error in self.errors_for(doc)))

    def test_external_endpoint_without_pin_fails(self):
        doc = copy.deepcopy(self.doc)
        doc["links"][1]["target"].pop("source_revision")
        self.assertTrue(any("must carry source revision" in error for error in self.errors_for(doc)))

    def test_relation_domain_mismatch_fails(self):
        doc = copy.deepcopy(self.doc)
        doc["links"][0]["source"]["kind"] = "fact"
        self.assertTrue(any("outside relation domain" in error for error in self.errors_for(doc)))

    def test_unknown_overlay_entity_fails(self):
        doc = copy.deepcopy(self.doc)
        doc["links"][0]["target"]["id"] = "K:not-registered"
        self.assertTrue(any("unknown overlay entity" in error for error in self.errors_for(doc)))

    def test_false_complete_concept_coverage_fails(self):
        doc = copy.deepcopy(self.doc)
        doc["links"][3]["qualifiers"]["completeness"] = "complete"
        self.assertTrue(any("single formalizes edge must be partial" in error for error in self.errors_for(doc)))

    def test_uncredited_established_by_link_fails(self):
        doc = copy.deepcopy(self.doc)
        doc["links"][2]["target"]["id"] = "authoritative-mathlib-modeq-family-v1"
        self.assertTrue(any("not credited by the fact evidence" in error for error in self.errors_for(doc)))


if __name__ == "__main__":
    unittest.main()
