from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_lean_official_construct_matrix",
    ROOT / "scripts" / "check-lean-official-construct-matrix.py",
)
assert SPEC and SPEC.loader
CHECK = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECK
SPEC.loader.exec_module(CHECK)


class LeanOfficialConstructMatrixTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = CHECK.load_manifest()

    def failures(self) -> list[str]:
        return CHECK.validate_manifest(self.data)

    def test_committed_product_registration_is_valid(self) -> None:
        self.assertEqual(self.failures(), [])

    def test_source_hash_drift_rejects(self) -> None:
        self.data["sources"]["positive"]["sha256"] = "0" * 64
        self.assertTrue(any("hash drift" in failure for failure in self.failures()))

    def test_historical_import_report_drift_rejects(self) -> None:
        self.data["historical_controls"][1]["expected_report"]["admitted_declarations"] = 12
        self.assertTrue(any("importer report drift" in failure for failure in self.failures()))

    def test_case_population_order_and_uniqueness_are_frozen(self) -> None:
        self.data["cases"].pop()
        self.assertTrue(any("case population drift" in failure for failure in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["cases"][0], self.data["cases"][1] = (
            self.data["cases"][1],
            self.data["cases"][0],
        )
        self.assertTrue(any("source-freeze contract drift" in failure for failure in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["cases"][1]["id"] = self.data["cases"][0]["id"]
        self.assertTrue(any("case IDs must be unique" in failure for failure in self.failures()))

    def test_stage_a_rejects_premature_wire_and_product_observations(self) -> None:
        self.data["stage"] = "source-frozen"
        self.data["product_measurement"] = {"rust": "not-yet"}
        failures = self.failures()
        self.assertTrue(any("must not contain Stage B" in failure for failure in failures))
        self.assertTrue(any("premature Stage B" in failure for failure in failures))
        self.assertTrue(any("must not contain product" in failure for failure in failures))

    def test_wire_inventory_and_case_link_drift_reject(self) -> None:
        stream = self.data["stage_b"]["streams"]["recursive-indexed"]
        stream["inventory"]["sha256"] = "0" * 64
        self.data["cases"][1]["stage_b_wire"] = None
        failures = self.failures()
        self.assertTrue(any("independent wire inventory drift" in failure for failure in failures))
        self.assertTrue(any("Stage B wire link drift" in failure for failure in failures))

    def test_stage_b_aggregate_and_reproduction_drift_reject(self) -> None:
        self.data["stage_b"]["new_stream_aggregate_bytes"] += 1
        self.data["stage_b"]["streams"]["mutual"]["export_runs"] = 1
        failures = self.failures()
        self.assertTrue(any("aggregate byte count drift" in failure for failure in failures))
        self.assertTrue(any("two byte-identical" in failure for failure in failures))

    def test_typed_product_outcome_and_publication_drift_reject(self) -> None:
        outcome = self.data["product_measurement"]["outcomes"]["nested"]
        outcome["variant"] = "Unsupported"
        outcome["completed_import_published"] = True
        self.data["cases"][4]["product_measurement"] = None
        failures = self.failures()
        self.assertTrue(any("typed product outcome drift" in failure for failure in failures))
        self.assertTrue(any("must not publish CompletedImport" in failure for failure in failures))
        self.assertTrue(any("product measurement link drift" in failure for failure in failures))

    def test_generated_assurance_matrix_is_deterministic_and_current(self) -> None:
        first = CHECK.render_matrix(self.data)
        second = CHECK.render_matrix(copy.deepcopy(self.data))
        self.assertEqual(first, second)
        self.assertEqual(CHECK.OUT_MD.read_text(encoding="utf-8"), first)
        rows = {row["id"]: row for row in CHECK.derive_matrix_rows(self.data)}
        self.assertEqual(
            {case_id: row["assurance_class"] for case_id, row in rows.items()},
            {
                "direct-recursive-control": "independently-admitted",
                "recursive-indexed": "dual-admitted-computation-checked",
                "reflexive-higher-order": "dual-admitted-computation-checked",
                "mutual": "dual-admitted-computation-checked",
                "nested": "official-export-inventory-only",
                "well-founded": "independently-admitted",
                "non-positive-source-negative": "official-source-rejected",
            },
        )
        self.assertIn("misclassified as malformed", first)
        self.assertIn("pre-elaborated root admitted through Acc.rec", first)
        self.assertIn("indexedCrossFamilyComputes", first)

    def test_tl212_computation_and_outcome_drift_reject(self) -> None:
        self.data["tl2_12_update"]["outcomes"]["recursive-indexed"]["report"][
            "admitted_declarations"
        ] = 13
        self.data["tl2_12_update"]["computations"]["reflexive-higher-order"][
            "sha256"
        ] = "0" * 64
        failures = self.failures()
        self.assertTrue(any("typed outcome/report drift" in failure for failure in failures))
        self.assertTrue(any("computation contract drift" in failure for failure in failures))
        self.assertTrue(any("computation hash drift" in failure for failure in failures))

    def test_tl213_computation_outcome_and_resource_drift_reject(self) -> None:
        self.data["tl2_13_update"]["outcomes"]["mutual"]["report"][
            "admitted_declarations"
        ] = 25
        self.data["tl2_13_update"]["computations"]["cross-family"]["sha256"] = (
            "0" * 64
        )
        self.data["tl2_13_update"]["computations"]["indexed-cross-family"][
            "reduction_checked"
        ] = False
        self.data["tl2_13_update"]["rust_test_threads"] = 2
        failures = self.failures()
        self.assertTrue(any("typed outcome/report drift" in failure for failure in failures))
        self.assertTrue(any("computation contract drift" in failure for failure in failures))
        self.assertTrue(any("computation hash drift" in failure for failure in failures))
        self.assertTrue(any("two checked TL2.13 computations" in failure for failure in failures))
        self.assertTrue(any("rust_test_threads drift" in failure for failure in failures))

    def test_impossible_assurance_promotions_reject(self) -> None:
        rows = {row["id"]: row for row in CHECK.derive_matrix_rows(self.data)}

        recursive = copy.deepcopy(rows["recursive-indexed"])
        recursive["assurance_class"] = "parsed-declined"
        self.assertTrue(
            any("independent-admission/class" in failure for failure in CHECK.validate_matrix_row(recursive))
        )

        nested = copy.deepcopy(rows["nested"])
        nested["assurance_class"] = "parsed-declined"
        self.assertTrue(
            any("Unsupported outcome" in failure for failure in CHECK.validate_matrix_row(nested))
        )

        control = copy.deepcopy(rows["direct-recursive-control"])
        control["assurance_class"] = "dual-admitted-computation-checked"
        self.assertTrue(
            any("computation/class" in failure for failure in CHECK.validate_matrix_row(control))
        )

    def test_unknown_fields_reject(self) -> None:
        self.data["cases"][0]["claim"] = "full Lean parity"
        self.assertTrue(any("fields drift" in failure for failure in self.failures()))

    def test_pin_resource_and_retention_drift_reject(self) -> None:
        for section, key, replacement, expected_message in (
            ("pins", "lean", {}, "pin drift"),
            ("resource_policy", "memory_max", "8G", "resource policy drift"),
            (
                "retention_policy",
                "per_stream_max_bytes",
                8_388_608,
                "retention policy drift",
            ),
        ):
            with self.subTest(section=section, key=key):
                mutated = copy.deepcopy(CHECK.load_manifest())
                mutated[section][key] = replacement
                self.data = mutated
                self.assertTrue(any(expected_message in failure for failure in self.failures()))

    def test_negative_must_remain_a_kernel_positivity_rejection(self) -> None:
        self.data["sources"]["negative"]["exit_status"] = 0
        self.data["sources"]["negative"]["official_source_outcome"] = "accepted"
        self.assertTrue(
            any("negative source rejection outcome drift" in failure for failure in self.failures())
        )


if __name__ == "__main__":
    unittest.main()
