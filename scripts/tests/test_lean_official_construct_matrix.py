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

    def test_committed_stage_a_registration_is_valid(self) -> None:
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

    def test_premature_wire_and_product_observations_reject(self) -> None:
        self.data["stage_b"] = {"observed": True}
        self.data["cases"][1]["stage_b_wire"] = {"sha256": "not-yet"}
        self.data["product_measurement"] = {"rust": "not-yet"}
        failures = self.failures()
        self.assertTrue(any("must not contain Stage B" in failure for failure in failures))
        self.assertTrue(any("premature Stage B" in failure for failure in failures))
        self.assertTrue(any("must not contain product" in failure for failure in failures))

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
