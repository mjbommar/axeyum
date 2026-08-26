"""Controls for the knowledge-overlay validator.

Every case selects its link BY RELATION, never by index. The index form broke
silently when ADR-0553 removed 24 links: four tests raised `StopIteration` or
asserted against a link that had changed relation underneath them, which is the
failure mode where a control stops testing what its name says.
"""

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
        cls.doc = json.loads((ROOT / "artifacts/autogenesis/knowledge-overlay-v1.json").read_text())

    def errors_for(self, doc):
        errors, _warnings = MODULE.validate_document(doc, ROOT)
        return errors

    @staticmethod
    def link_with(doc, relation):
        return next(link for link in doc["links"] if link["relation"] == relation)

    def test_committed_overlay_passes(self):
        self.assertEqual(self.errors_for(self.doc), [])

    def test_unknown_local_fact_fails(self):
        doc = copy.deepcopy(self.doc)
        self.link_with(doc, "realizes-capability")["source"] = {
            "namespace": "axeyum-fact",
            "kind": "fact",
            "id": "F:not-a-real-fact",
        }
        self.assertTrue(any("unknown fact" in error for error in self.errors_for(doc)))

    def test_relation_domain_mismatch_fails(self):
        doc = copy.deepcopy(self.doc)
        self.link_with(doc, "realizes-capability")["source"]["kind"] = "fact"
        self.assertTrue(any("outside relation domain" in error for error in self.errors_for(doc)))

    def test_unknown_overlay_entity_fails(self):
        doc = copy.deepcopy(self.doc)
        self.link_with(doc, "realizes-capability")["target"]["id"] = "K:not-registered"
        self.assertTrue(any("unknown overlay entity" in error for error in self.errors_for(doc)))

    def test_uncredited_established_by_link_fails(self):
        doc = copy.deepcopy(self.doc)
        link = self.link_with(doc, "established-by")
        # Credit the fact to an operation its own evidence does not name.
        other = next(
            l["target"]["id"]
            for l in doc["links"]
            if l["relation"] == "established-by" and l["target"]["id"] != link["target"]["id"]
        )
        link["target"]["id"] = other
        self.assertTrue(
            any("not credited by the fact evidence" in error for error in self.errors_for(doc))
        )

    def test_unknown_local_concept_fails(self):
        doc = copy.deepcopy(self.doc)
        self.link_with(doc, "formalizes")["target"]["id"] = "C:not-registered"
        self.assertTrue(any("unknown overlay entity" in error for error in self.errors_for(doc)))

    def test_formalizes_full_coverage_fails(self):
        doc = copy.deepcopy(self.doc)
        self.link_with(doc, "formalizes")["qualifiers"]["completeness"] = "complete"
        self.assertTrue(
            any("completeness must be partial" in error for error in self.errors_for(doc))
        )

    def test_formalizes_non_theorem_kernel_source_fails(self):
        doc = copy.deepcopy(self.doc)
        link = self.link_with(doc, "formalizes")
        link["source"]["id"] = "Complex.normSq"
        self.assertTrue(
            any("kernel source is not a theorem" in error for error in self.errors_for(doc))
        )

    def test_formalizes_assumption_bearing_kernel_source_fails(self):
        doc = copy.deepcopy(self.doc)
        link = self.link_with(doc, "formalizes")
        link["source"]["id"] = "AxReal"
        self.assertTrue(any("nonempty axiom footprint" in error for error in self.errors_for(doc)))

    def test_formalizes_requires_human_review(self):
        doc = copy.deepcopy(self.doc)
        self.link_with(doc, "formalizes")["assurance"] = "heuristic"
        self.assertTrue(
            any("assurance must be human-reviewed" in error for error in self.errors_for(doc))
        )

    # --- ADR-0553: the overlay may not name anything outside this checkout ---

    def test_external_repository_source_rejected(self):
        doc = copy.deepcopy(self.doc)
        doc["sources"].append(
            {
                "id": "sibling",
                "kind": "external-repository",
                "revision_policy": "pinned",
                "revision": "0" * 40,
                "path_hint": "../sibling",
            }
        )
        self.assertTrue(
            any("is not one of" in error and "kind" in error for error in self.errors_for(doc))
        )

    def test_escaping_path_hint_rejected(self):
        doc = copy.deepcopy(self.doc)
        doc["sources"][0]["path_hint"] = "../sibling"
        self.assertTrue(any("path_hint" in error for error in self.errors_for(doc)))

    def test_external_pinned_namespace_rejected(self):
        doc = copy.deepcopy(self.doc)
        doc["namespaces"].append(
            {
                "id": "sibling",
                "source_id": "axeyum",
                "entity_kinds": ["fact"],
                "resolution": "external-pinned",
                "path": "graph",
            }
        )
        self.assertTrue(any("external-pinned" in error for error in self.errors_for(doc)))

    def test_endpoint_source_revision_rejected(self):
        doc = copy.deepcopy(self.doc)
        self.link_with(doc, "realizes-capability")["target"]["source_revision"] = "0" * 40
        self.assertTrue(any("source_revision" in error for error in self.errors_for(doc)))


if __name__ == "__main__":
    unittest.main()
