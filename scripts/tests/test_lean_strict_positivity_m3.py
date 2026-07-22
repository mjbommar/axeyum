from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_lean_strict_positivity_m3",
    ROOT / "scripts" / "check-lean-strict-positivity-m3.py",
)
assert SPEC and SPEC.loader
CHECK = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECK
SPEC.loader.exec_module(CHECK)


class LeanStrictPositivityM3Tests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = CHECK.load_manifest()

    def failures(self) -> list[str]:
        return CHECK.validate_manifest(self.data)

    def test_committed_observations_are_valid(self) -> None:
        self.assertEqual(self.failures(), [])

    def test_source_freeze_and_revision_drift_reject(self) -> None:
        self.data["source_freeze"]["sha256"] = "0" * 64
        self.assertTrue(any("source freeze hash drift" in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["implementation_revision"] = "0" * 40
        self.assertTrue(any("revision drift" in item for item in self.failures()))

    def test_official_population_order_and_outcomes_are_frozen(self) -> None:
        self.data["official_runs"].pop()
        self.assertTrue(any("run population" in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["official_runs"][1]["outcome"] = "accepted"
        self.assertTrue(any("run population" in item for item in self.failures()))

    def test_diagnostic_stream_and_resource_envelope_are_frozen(self) -> None:
        self.data["official_runs"][2]["diagnostic_stream"] = None
        self.assertTrue(any("run population" in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["official_runs"][0]["max_rss_kib"] = 4 * 1024 * 1024 + 1
        self.assertTrue(any("resource envelope" in item for item in self.failures()))

    def test_synthetic_assurance_and_no_publication_are_frozen(self) -> None:
        self.data["synthetic_importer"]["assurance"] = "official-wire"
        self.assertTrue(any("synthetic importer" in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["synthetic_importer"]["completed_import_published"] = True
        self.assertTrue(any("synthetic importer" in item for item in self.failures()))

    def test_construct_matrix_regression_cannot_be_promoted_or_rebound(self) -> None:
        self.data["construct_matrix_regression"]["outcomes_unchanged_at_m3"] = False
        self.assertTrue(any("construct-matrix observation" in item for item in self.failures()))

        mutated = copy.deepcopy(CHECK.load_manifest())
        mutated["construct_matrix_regression"]["current_registration_sha256"] = "0" * 64
        self.data = mutated
        self.assertTrue(any("construct-matrix observation" in item for item in self.failures()))


if __name__ == "__main__":
    unittest.main()
