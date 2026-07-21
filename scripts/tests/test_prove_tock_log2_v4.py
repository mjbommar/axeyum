import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path

from scripts.tests.test_prove_tock_log2_v3 import valid_v3_output


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/prove-tock-log2-v4.py"
SPEC = importlib.util.spec_from_file_location("prove_tock_log2_v4", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
PRODUCER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PRODUCER
SPEC.loader.exec_module(PRODUCER)


def capture_error(callable_):
    with unittest.TestCase().assertRaises(PRODUCER.CaptureError) as raised:
        callable_()
    return raised.exception.stage, raised.exception.kind


def prefixed_output() -> str:
    output = valid_v3_output()
    return PRODUCER.HARNESS_PREFIX + output


class ProveTockLog2V4Tests(unittest.TestCase):
    def test_live_lineage_registration_and_capture_validate_prequery(self):
        negative = PRODUCER.validate_lineage()
        registration = PRODUCER.read_registration(PRODUCER.DEFAULT_REGISTRATION)
        capture = PRODUCER.BASE.validate_capture(registration)
        self.assertEqual(negative["error"]["observed_proof_rows"], 7)
        self.assertEqual(registration["schema"], PRODUCER.REGISTRATION_SCHEMA)
        self.assertEqual(
            capture["capture_identity_sha256"],
            registration["capture"]["identity_sha256"],
        )

    def test_lineage_rejects_mutated_v3_negative(self):
        negative = json.loads(PRODUCER.V3_NEGATIVE.read_text(encoding="utf-8"))
        negative["error"]["observed_proof_rows"] = 8
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "negative.json"
            path.write_text(json.dumps(negative), encoding="utf-8")
            self.assertEqual(
                capture_error(
                    lambda: PRODUCER.validate_lineage(
                        PRODUCER.V3_REGISTRATION,
                        PRODUCER.V3_PREFLIGHT,
                        path,
                    )
                ),
                ("lineage", "v3_negative_hash"),
            )

    def test_exact_harness_prefix_normalizes_and_full_parser_accepts(self):
        parsed = PRODUCER.parse_runner_output(prefixed_output())
        self.assertEqual(len(parsed["proofs"]), 8)
        self.assertEqual(len(parsed["controls"]), 6)

    def test_wrong_duplicate_and_nonproof_prefixes_are_rejected(self):
        wrong = "test wrong ... " + valid_v3_output()
        self.assertEqual(
            capture_error(lambda: PRODUCER.normalize_runner_output(wrong)),
            ("result", "marker_prefix"),
        )
        duplicated = prefixed_output().replace(
            "|terms=100|wall_us=10",
            "|terms=100|wall_us=10|TOCK_PROOF|duplicate=1",
            1,
        )
        self.assertEqual(
            capture_error(lambda: PRODUCER.normalize_runner_output(duplicated)),
            ("result", "marker_multiplicity"),
        )
        prefixed_control = PRODUCER.HARNESS_PREFIX + valid_v3_output().replace(
            "TOCK_PROOF|", "TOCK_CONTROL|", 1
        )
        self.assertEqual(
            capture_error(lambda: PRODUCER.normalize_runner_output(prefixed_control)),
            ("result", "marker_prefix"),
        )

    def test_registration_preserves_v3_policy_and_inputs(self):
        v3 = json.loads(PRODUCER.V3_REGISTRATION.read_text(encoding="utf-8"))
        v4 = json.loads(PRODUCER.DEFAULT_REGISTRATION.read_text(encoding="utf-8"))
        for field in (
            "archive_policy",
            "canonical",
            "capture",
            "command",
            "expected_rows",
            "resource_scope",
            "solver",
            "source_files",
            "tools",
        ):
            self.assertEqual(v4[field], v3[field], field)

    def test_no_official_output_exists_prequery(self):
        self.assertFalse(PRODUCER.DEFAULT_OUTPUT.exists())


if __name__ == "__main__":
    unittest.main()
