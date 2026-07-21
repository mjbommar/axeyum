import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/capture-tock-log2-v3.py"
SPEC = importlib.util.spec_from_file_location("capture_tock_log2_v3", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
CAPTURE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CAPTURE
SPEC.loader.exec_module(CAPTURE)


def capture_error(callable_):
    with unittest.TestCase().assertRaises(CAPTURE.CaptureError) as raised:
        callable_()
    return raised.exception.stage, raised.exception.kind


class CaptureTockLog2V3Tests(unittest.TestCase):
    def test_registration_pins_v2_registration_negative_and_lineage(self):
        registration = CAPTURE.read_registration(CAPTURE.DEFAULT_REGISTRATION)
        CAPTURE.validate_registration(registration)
        self.assertEqual(
            registration["upstream"][CAPTURE.V2_NEGATIVE_SHA_FIELD],
            CAPTURE.V2_NEGATIVE_IDENTITY["sha256"],
        )
        overlay = json.loads(
            CAPTURE.DEFAULT_REGISTRATION.read_text(encoding="utf-8")
        )
        for field in ("capture_v2_registration", "capture_v2_negative"):
            candidate = json.loads(json.dumps(overlay))
            candidate[field]["sha256"] = "0" * 64
            with tempfile.TemporaryDirectory() as raw:
                path = Path(raw) / "registration.json"
                path.write_text(json.dumps(candidate), encoding="utf-8")
                self.assertEqual(
                    capture_error(lambda: CAPTURE.read_registration(path)),
                    ("registration", field),
                )

    def test_structural_replay_receives_full_cache_registration_only(self):
        merged = {
            "cache_result": {"probe": {"active_resolution_sha256": "active"}},
            "marker": "capture-registration",
        }
        full = {
            "expected_lock_packages": 169,
            "marker": "cache-registration",
        }
        inventory = {"sha256": "inventory"}

        def probe(registration, source, cache, target):
            self.assertIs(registration, full)
            self.assertEqual(registration["expected_lock_packages"], 169)
            self.assertNotIn("expected_lock_packages", merged)
            return {"active_resolution_sha256": "active"}

        with (
            mock.patch.object(
                CAPTURE.V2, "validate_local_cache", return_value=inventory
            ),
            mock.patch.object(
                CAPTURE.V2.V5, "read_registration", return_value=full
            ),
            mock.patch.object(CAPTURE.V2.V5, "validate_registration"),
            mock.patch.object(CAPTURE.V2.V5, "structural_probe", side_effect=probe),
            mock.patch.object(
                CAPTURE.V2.V5.V4, "inventory_cache", return_value=inventory
            ),
        ):
            CAPTURE.validate_cache(merged, Path("/source"), Path("/target"))
        self.assertEqual(merged["marker"], "capture-registration")

    def test_wrong_lock_count_fails_before_structural_probe(self):
        full = {"expected_lock_packages": 168}
        with (
            mock.patch.object(
                CAPTURE.V2.V5, "read_registration", return_value=full
            ),
            mock.patch.object(CAPTURE.V2.V5, "validate_registration"),
            mock.patch.object(CAPTURE.V2.V5, "structural_probe") as probe,
        ):
            self.assertEqual(
                capture_error(CAPTURE.full_cache_registration),
                ("cache", "expected_lock_packages"),
            )
            probe.assert_not_called()

    def test_probe_and_post_probe_inventory_drift_remain_rejected(self):
        registration = {"cache_result": {"probe": {"packages": 162}}}
        full = {"expected_lock_packages": 169}
        before = {"sha256": "before"}
        with (
            mock.patch.object(
                CAPTURE.V2, "validate_local_cache", return_value=before
            ),
            mock.patch.object(
                CAPTURE.V2.V5, "read_registration", return_value=full
            ),
            mock.patch.object(CAPTURE.V2.V5, "validate_registration"),
            mock.patch.object(
                CAPTURE.V2.V5,
                "structural_probe",
                return_value={"packages": 161},
            ),
        ):
            self.assertEqual(
                capture_error(
                    lambda: CAPTURE.validate_cache(
                        registration, Path("/source"), Path("/target")
                    )
                ),
                ("cache", "probe_drift"),
            )
        with (
            mock.patch.object(
                CAPTURE.V2, "validate_local_cache", return_value=before
            ),
            mock.patch.object(
                CAPTURE.V2.V5, "read_registration", return_value=full
            ),
            mock.patch.object(CAPTURE.V2.V5, "validate_registration"),
            mock.patch.object(
                CAPTURE.V2.V5,
                "structural_probe",
                return_value={"packages": 162},
            ),
            mock.patch.object(
                CAPTURE.V2.V5.V4,
                "inventory_cache",
                return_value={"sha256": "after"},
            ),
        ):
            self.assertEqual(
                capture_error(
                    lambda: CAPTURE.validate_cache(
                        registration, Path("/source"), Path("/target")
                    )
                ),
                ("cache", "probe_inventory_drift"),
            )

    def test_run_patches_only_v2_policy_and_restores_it(self):
        sentinel = {"status": "accepted", "identity_sha256": "identity"}

        def delegated(_args):
            self.assertIs(CAPTURE.V2.read_registration, CAPTURE.read_registration)
            self.assertIs(
                CAPTURE.V2.validate_registration, CAPTURE.validate_registration
            )
            self.assertIs(CAPTURE.V2.validate_cache, CAPTURE.validate_cache)
            self.assertEqual(CAPTURE.V2.RESULT_SCHEMA, CAPTURE.RESULT_SCHEMA)
            return sentinel

        with mock.patch.object(CAPTURE.V2, "run_capture", side_effect=delegated):
            self.assertIs(
                CAPTURE.run_capture(CAPTURE.parse_args([])),
                sentinel,
            )
        self.assertIs(CAPTURE.V2.read_registration, CAPTURE.V2_READ_REGISTRATION)
        self.assertIs(
            CAPTURE.V2.validate_registration,
            CAPTURE.V2_VALIDATE_REGISTRATION,
        )
        self.assertIs(CAPTURE.V2.validate_cache, CAPTURE.V2_VALIDATE_CACHE)
        self.assertEqual(CAPTURE.V2.RESULT_SCHEMA, CAPTURE.V2_RESULT_SCHEMA)


if __name__ == "__main__":
    unittest.main()
