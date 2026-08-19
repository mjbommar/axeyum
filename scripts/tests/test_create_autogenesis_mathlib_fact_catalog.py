from __future__ import annotations

import copy
import hashlib
import importlib.util
import pathlib
import unittest
from unittest import mock


SCRIPT = pathlib.Path(__file__).parents[1] / "create-autogenesis-mathlib-fact-catalog.py"
SPEC = importlib.util.spec_from_file_location("create_autogenesis_mathlib_fact_catalog", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class MathlibFactCatalogTests(unittest.TestCase):
    def inputs(self):
        review = {
            "state": "reviewed-groups-not-frozen-split",
            "coverage": {"evaluation_eligible_candidates": 2},
            "reviewed_candidates": [
                {
                    "candidate_id": "a" * 64,
                    "dependency_component_id": "component",
                    "disposition": "evaluation-eligible",
                    "domain": "Nat",
                    "name": "Nat.a",
                    "statement": "∀ n : ℕ, n = n",
                    "theme": "family-a",
                },
                {
                    "candidate_id": "b" * 64,
                    "dependency_component_id": "component",
                    "disposition": "evaluation-eligible",
                    "domain": "Nat",
                    "name": "Nat.b",
                    "statement": "∀ n : ℕ, n ≤ n",
                    "theme": "family-a",
                },
            ],
            "mutations": [
                {
                    "dependency_component_id": "component",
                    "domain": "Nat",
                    "mutation_class": "relation-strengthening",
                    "mutation_id": "M:" + "c" * 24,
                    "source_candidate_id": "a" * 64,
                    "source_name": "Nat.a",
                    "statement": "∀ n : ℕ, n < n",
                    "theme": "family-a",
                }
            ],
        }
        review["review_sha256"] = MODULE.digest(review)
        components = {
            "components": [
                {
                    "component_id": "component",
                    "members": [{"name": "Nat.a"}, {"name": "Nat.b"}],
                    "edges": [{"dependent": "Nat.b", "dependency": "Nat.a"}],
                }
            ]
        }
        components["components_sha256"] = MODULE.digest(components)
        review["dependency_components_sha256"] = components["components_sha256"]
        review["review_sha256"] = MODULE.digest(
            {key: value for key, value in review.items() if key != "review_sha256"}
        )
        return review, components

    def build(self, review, components):
        with mock.patch.object(MODULE, "SURFACE_NORMALIZATIONS", {}):
            surface_sha = hashlib.sha256(MODULE.lean_surface_module(review).encode()).hexdigest()
            with mock.patch.object(MODULE, "SURFACE_ATTESTATION_SHA256", surface_sha):
                return MODULE.build(review, components)

    def test_open_fact_projection_preserves_authorship_and_dependencies(self) -> None:
        review, components = self.inputs()
        catalog, facts = self.build(review, components)
        source_a = facts[MODULE.source_fact_id(review["reviewed_candidates"][0])]
        source_b = facts[MODULE.source_fact_id(review["reviewed_candidates"][1])]
        mutation = facts[MODULE.mutation_fact_id(review["mutations"][0])]
        self.assertEqual(source_a["epistemic_status"], "open")
        self.assertEqual(source_a["external_status"], "proved")
        self.assertTrue(source_a["provenance"]["prior_art"])
        self.assertEqual(source_b["depends_on"], [source_a["id"]])
        self.assertEqual(mutation["external_status"], "unknown")
        self.assertEqual(mutation["depends_on"], [])
        self.assertNotIn("proof_route", source_a)
        self.assertEqual(catalog["coverage"]["facts"], 3)

    def test_surface_module_declares_types_without_proofs(self) -> None:
        review, _ = self.inputs()
        with mock.patch.object(MODULE, "SURFACE_NORMALIZATIONS", {}):
            text = MODULE.lean_surface_module(review)
        self.assertEqual(text.count("\naxiom "), 3)
        self.assertNotIn("theoremInfo.value", text)
        self.assertNotIn(":= by", text)
        self.assertNotIn("exact ", text)

    def test_surface_normalization_is_explicit_and_statement_preserving(self) -> None:
        original = "∀ (b : ℕ), Monotone fun a => a.choose b"
        normalized = MODULE.surface_statement("Nat.choose_mono", original)
        self.assertNotEqual(normalized, original)
        self.assertIn("fun a : ℕ", normalized)
        self.assertEqual(MODULE.surface_statement("Nat.unrelated", original), original)

    def test_review_and_component_identity_must_match(self) -> None:
        review, components = self.inputs()
        review["dependency_components_sha256"] = "0" * 64
        review["review_sha256"] = MODULE.digest(
            {key: value for key, value in review.items() if key != "review_sha256"}
        )
        with self.assertRaisesRegex(MODULE.CatalogError, "differ"):
            self.build(review, components)

    def test_unattested_surface_change_fails_closed(self) -> None:
        review, components = self.inputs()
        with mock.patch.object(MODULE, "SURFACE_NORMALIZATIONS", {}), mock.patch.object(
            MODULE, "SURFACE_ATTESTATION_SHA256", "0" * 64
        ):
            with self.assertRaisesRegex(MODULE.CatalogError, "real-Lean attestation"):
                MODULE.build(review, components)

    def test_rehashed_catalog_mutation_still_fails_exact_verification(self) -> None:
        review, components = self.inputs()
        catalog, _ = self.build(review, components)
        actual = copy.deepcopy(catalog)
        actual["facts"][0]["statement_shape"] = "invented"
        actual["catalog_sha256"] = MODULE.digest(
            {key: value for key, value in actual.items() if key != "catalog_sha256"}
        )
        with self.assertRaisesRegex(MODULE.CatalogError, "stale or mutated"):
            MODULE.verify_catalog(actual, catalog)


if __name__ == "__main__":
    unittest.main()
