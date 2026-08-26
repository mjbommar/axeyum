from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "open_fixed_palette",
    ROOT / "scripts/measure-autogenesis-open-fixed-palette.py",
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OpenFixedPaletteTests(unittest.TestCase):
    def test_palette_is_sorted_unique_and_target_independent(self) -> None:
        self.assertEqual(tuple(sorted(set(MODULE.CANDIDATES))), MODULE.CANDIDATES)
        self.assertNotIn("Nat.fib_mono", MODULE.CANDIDATES)

    def test_capsule_name_is_stable(self) -> None:
        self.assertEqual(
            MODULE.capsule_path(Path("/packs"), "F:ml430-nat-foo-deadbeef"),
            Path("/packs/F-ml430-nat-foo-deadbeef.ndjson"),
        )

    def test_held_out_rows_are_excluded_before_capsule_access(self) -> None:
        mapping = {"F:train": "T.train", "F:held": "T.held"}
        nursery = {
            "entries": [
                {"fact_id": "F:train", "partition": "train"},
                {"fact_id": "F:held", "partition": "held-out"},
            ]
        }
        eligible, excluded = MODULE.eligible_mapping(mapping, nursery)
        self.assertEqual(eligible, {"F:train": "T.train"})
        self.assertEqual(excluded, ["F:held"])

    def test_unknown_nursery_identity_fails_closed(self) -> None:
        with self.assertRaisesRegex(ValueError, "absent from the nursery"):
            MODULE.eligible_mapping({"F:unknown": "T"}, {"entries": []})

    def test_candidate_absence_is_a_typed_import_rejection(self) -> None:
        self.assertEqual(
            MODULE.classify_statement_import_error(
                'candidate declaration "Nat.mod_eq_add_left" occurs 0 times; expected one'
            ),
            {
                "reason_kind": "CandidateDeclarationUnavailable",
                "candidate_declaration": "Nat.mod_eq_add_left",
                "candidate_occurrence_count": 0,
            },
        )

    def test_unknown_import_error_is_not_misclassified(self) -> None:
        self.assertEqual(
            MODULE.classify_statement_import_error("new failure shape"),
            {
                "reason_kind": "UnclassifiedStatementImportError",
                "message": "new failure shape",
            },
        )

    def test_candidate_trusted_closure_is_a_typed_import_rejection(self) -> None:
        self.assertEqual(
            MODULE.classify_statement_import_error(
                'candidate declaration "Int.add_assoc" reaches 1 trusted declaration(s)'
            ),
            {
                "reason_kind": "CandidateClosureReachesTrustedDeclaration",
                "candidate_declaration": "Int.add_assoc",
                "candidate_trusted_declaration_count": 1,
            },
        )

    def test_population_mapping_is_exact_and_unique(self) -> None:
        self.assertEqual(
            MODULE.population_mapping(
                {
                    "outcomes": [
                        {"fact_id": "F:a", "target_definition": "T.a"},
                        {"fact_id": "F:b", "target_definition": "T.b"},
                    ]
                }
            ),
            {"F:a": "T.a", "F:b": "T.b"},
        )
        with self.assertRaisesRegex(ValueError, "duplicate"):
            MODULE.population_mapping(
                {
                    "outcomes": [
                        {"fact_id": "F:a", "target_definition": "T.a"},
                        {"fact_id": "F:a", "target_definition": "T.a"},
                    ]
                }
            )

    def test_population_mapping_fails_closed_on_malformed_rows(self) -> None:
        with self.assertRaisesRegex(ValueError, "outcomes array"):
            MODULE.population_mapping({})
        with self.assertRaisesRegex(ValueError, "fact_id and target_definition"):
            MODULE.population_mapping({"outcomes": [{"fact_id": "F:a"}]})


if __name__ == "__main__":
    unittest.main()
