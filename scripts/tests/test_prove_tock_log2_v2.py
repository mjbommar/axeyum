import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/prove-tock-log2-v2.py"
SPEC = importlib.util.spec_from_file_location("prove_tock_log2_v2", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
PRODUCER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PRODUCER
SPEC.loader.exec_module(PRODUCER)


def capture_error(callable_):
    with unittest.TestCase().assertRaises(PRODUCER.CaptureError) as raised:
        callable_()
    return raised.exception.stage, raised.exception.kind


class ProveTockLog2V2Tests(unittest.TestCase):
    def test_live_lineage_and_registration_validate_prequery(self):
        negative = PRODUCER.validate_lineage()
        registration = PRODUCER.read_registration(PRODUCER.DEFAULT_REGISTRATION)
        self.assertEqual(negative["outputs"]["property_queries"], 0)
        self.assertEqual(registration["schema"], PRODUCER.REGISTRATION_SCHEMA)
        self.assertEqual(
            next(
                row["sha256"]
                for row in registration["source_files"]
                if row["path"] == "Cargo.lock"
            ),
            PRODUCER.CORRECTED_LOCK_SHA256,
        )

    def test_lineage_rejects_mutated_negative(self):
        original = json.loads(PRODUCER.V1_NEGATIVE.read_text(encoding="utf-8"))
        original["outputs"]["property_queries"] = 1
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "negative.json"
            path.write_text(json.dumps(original), encoding="utf-8")
            self.assertEqual(
                capture_error(
                    lambda: PRODUCER.validate_lineage(
                        PRODUCER.V1_REGISTRATION,
                        path,
                    )
                ),
                ("lineage", "v1_negative_hash"),
            )

    def test_v2_schema_and_output_are_distinct(self):
        self.assertNotEqual(
            PRODUCER.REGISTRATION_SCHEMA,
            "axeyum.tock-log2-proof-v1-registration.v1",
        )
        self.assertNotEqual(PRODUCER.DEFAULT_OUTPUT, PRODUCER.BASE.DEFAULT_OUTPUT)
        self.assertEqual(PRODUCER.DEFAULT_OUTPUT.name, "proof-v2")

    def test_registration_preserves_v1_semantics_and_policy(self):
        v1 = json.loads(PRODUCER.V1_REGISTRATION.read_text(encoding="utf-8"))
        v2 = json.loads(PRODUCER.DEFAULT_REGISTRATION.read_text(encoding="utf-8"))
        for field in (
            "archive_policy",
            "canonical",
            "capture",
            "command",
            "expected_rows",
            "resource_scope",
            "solver",
            "tools",
        ):
            self.assertEqual(v2[field], v1[field], field)
        v1_sources = {row["path"]: row["sha256"] for row in v1["source_files"]}
        v2_sources = {row["path"]: row["sha256"] for row in v2["source_files"]}
        self.assertEqual(set(v2_sources), set(v1_sources))
        self.assertEqual(v2_sources["Cargo.toml"], v1_sources["Cargo.toml"])
        self.assertEqual(
            v2_sources["crates/axeyum-verify/Cargo.toml"],
            v1_sources["crates/axeyum-verify/Cargo.toml"],
        )
        self.assertNotEqual(v2_sources["Cargo.lock"], v1_sources["Cargo.lock"])
        self.assertEqual(v2_sources["Cargo.lock"], PRODUCER.CORRECTED_LOCK_SHA256)

    def test_no_official_output_exists_prequery(self):
        self.assertFalse(PRODUCER.DEFAULT_OUTPUT.exists())
        self.assertFalse(PRODUCER.BASE.DEFAULT_OUTPUT.exists())


if __name__ == "__main__":
    unittest.main()
