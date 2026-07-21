"""Focused tests for the G1 cross-regime provenance generator."""

from __future__ import annotations

import copy
import importlib.util
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "gen-measurement-provenance.py"
SPEC = importlib.util.spec_from_file_location("gen_measurement_provenance", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class MeasurementProvenanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.manifest = MODULE.load_json(MODULE.MANIFEST)
        cls.report = MODULE.build_report(cls.manifest)

    def test_current_denominators_and_overlap_are_pinned(self) -> None:
        score = self.report["summary"]["regression_scoreboard"]
        public = self.report["summary"]["public_inventory"]
        overlap = self.report["summary"]["cross_regime"]
        self.assertEqual(
            (
                score["rows"],
                score["raw_cases"],
                score["file_backed_occurrences"],
                score["unique_normalized_ids"],
                score["unique_content_sha256"],
                score["exact_duplicate_groups"],
                score["exact_duplicate_excess"],
                score["aggregate_only_cases"],
            ),
            (35, 992, 927, 837, 778, 58, 59, 65),
        )
        self.assertEqual(
            (public["rows"], public["raw_cases"], public["unique_content_sha256"]),
            (18, 228, 228),
        )
        self.assertEqual(overlap["unique_content_overlap"], 99)
        self.assertEqual(len(self.report["cross_regime_exact_overlap"]), 99)

    def test_no_row_inherits_official_or_neutral_credit(self) -> None:
        self.assertEqual(len(self.report["rows"]), 53)
        for row in self.report["rows"]:
            self.assertFalse(row["official_selection"])
            self.assertGreater(row["wall_limit_s"], 0)
            self.assertEqual(
                row["neutral_oracle_status"], "absent-on-exact-population"
            )

    def test_identity_and_coverage_layers_remain_distinct(self) -> None:
        self.assertEqual(
            MODULE.normalize_scoreboard_id(
                "corpus/x/non-incremental/QF_UF/family/a.smt2"
            ),
            "QF_UF/family/a.smt2",
        )
        self.assertEqual(MODULE.coverage_class(8, 10), "decide-strong")
        self.assertEqual(MODULE.coverage_class(2, 10), "partial")
        self.assertEqual(MODULE.coverage_class(1, 10), "frontier")

    def test_manifest_cannot_silently_claim_official_selection(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        mutated["regimes"][0]["official_selection"] = True
        with self.assertRaisesRegex(ValueError, "not official selections"):
            MODULE.validate_manifest(mutated)

    def test_expected_population_drift_fails(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        mutated["regimes"][0]["expected_raw_cases"] += 1
        with self.assertRaisesRegex(ValueError, "scoreboard population drift"):
            MODULE.build_report(mutated)


if __name__ == "__main__":
    unittest.main()
