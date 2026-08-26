import importlib.util
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "kernel_lemma_search_index",
    ROOT / "scripts/gen-autogenesis-kernel-lemma-search-index.py",
)
assert SPEC and SPEC.loader
INDEX = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(INDEX)


class KernelLemmaSearchIndexTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = INDEX.build()
        cls.rows = {
            row["kernel_declaration_id"]: row for row in cls.data["lemmas"]
        }

    def test_every_kernel_theorem_appears_exactly_once(self):
        self.assertEqual(len(self.rows), len(self.data["lemmas"]))
        self.assertEqual(
            len(self.rows), self.data["census"]["kernel_theorems"]
        )

    def test_reverse_edges_are_exact(self):
        for theorem, row in self.rows.items():
            for dependency in row["direct_theorem_dependencies"]:
                self.assertIn(theorem, self.rows[dependency]["direct_theorem_dependents"])
            for dependent in row["direct_theorem_dependents"]:
                self.assertIn(theorem, self.rows[dependent]["direct_theorem_dependencies"])

    def test_dependency_depth_strictly_increases_across_edges(self):
        for row in self.rows.values():
            for dependency in row["direct_theorem_dependencies"]:
                self.assertGreater(
                    row["dependency_depth"], self.rows[dependency]["dependency_depth"]
                )

    def test_exact_fact_links_resolve_and_unresolved_are_retained(self):
        linked = {
            fact_id for row in self.rows.values() for fact_id in row["exact_fact_ids"]
        }
        self.assertEqual(
            len(linked), self.data["census"]["distinct_exactly_linked_facts"]
        )
        self.assertGreater(len(linked), 0)
        unresolved = self.data["unresolved_prefixed_kernel_evidence"]
        self.assertEqual(
            len(unresolved),
            self.data["census"]["unresolved_prefixed_kernel_evidence"],
        )
        self.assertGreater(len(unresolved), 0)
        self.assertEqual(
            sum(self.data["census"]["unresolved_reason_counts"].values()),
            len(unresolved),
        )

    def test_non_theorem_identity_is_distinguished_from_absence(self):
        row = next(
            row
            for row in self.data["unresolved_prefixed_kernel_evidence"]
            if row["fact_id"] == "F:rat-normalize-reduces"
        )
        self.assertIn("definition declaration, not a theorem", row["reason"])

    def test_search_rows_confer_no_proof_authority(self):
        self.assertTrue(
            all(row["search_authority"].startswith("candidate-only") for row in self.rows.values())
        )

    def test_explicit_declaration_identity_precedes_legacy_evidence_id(self):
        self.assertEqual(
            INDEX.exact_kernel_declaration(
                {
                    "id": "kernel-le_trans",
                    "kernel_declaration": "Nat.le_trans",
                }
            ),
            "Nat.le_trans",
        )

    def test_plural_declaration_identity_precedes_singular_and_legacy(self):
        self.assertEqual(
            INDEX.exact_kernel_declarations(
                {
                    "id": "kernel-invented",
                    "kernel_declaration": "Also.invented",
                    "kernel_declarations": ["And.left", "And.right"],
                }
            ),
            ("And.left", "And.right"),
        )

    def test_legacy_fully_qualified_evidence_id_remains_supported(self):
        self.assertEqual(
            INDEX.exact_kernel_declaration({"id": "kernel-Nat.le_trans"}),
            "Nat.le_trans",
        )


if __name__ == "__main__":
    unittest.main()
