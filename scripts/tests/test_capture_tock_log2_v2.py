import importlib.util
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/capture-tock-log2-v2.py"
SPEC = importlib.util.spec_from_file_location("capture_tock_log2_v2", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
CAPTURE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CAPTURE
SPEC.loader.exec_module(CAPTURE)


def capture_error(callable_):
    with unittest.TestCase().assertRaises(CAPTURE.CaptureError) as raised:
        callable_()
    return raised.exception.stage, raised.exception.kind


class CaptureTockLog2V2Tests(unittest.TestCase):
    def test_root_and_environment_remove_only_ambient_cargo(self):
        self.assertNotIn("/home/mjbommar/.cargo", CAPTURE.EXPECTED_ROOT)
        cargo_home = dict(CAPTURE.EXPECTED_ENVIRONMENT)["CARGO_HOME"]
        self.assertEqual(cargo_home, "/axeyum-vroot/cache")
        base = dict(CAPTURE.V1.EXPECTED_ENVIRONMENT)
        current = dict(CAPTURE.EXPECTED_ENVIRONMENT)
        self.assertEqual(set(base), set(current))
        for name in base:
            if name != "CARGO_HOME":
                self.assertEqual(base[name], current[name])

    def test_build_namespace_mounts_cache_read_only_once(self):
        registration = {"tools": {"bwrap": {"path": "/usr/bin/bwrap"}}}
        command = CAPTURE.bwrap_command(
            registration, Path("/source"), Path("/target"), ["cargo", "rustc"]
        )
        cache = str(CAPTURE.LOCAL_CACHE_HOME)
        self.assertEqual(command.count(cache), 1)
        index = command.index(cache)
        self.assertEqual(command[index - 1], "--ro-bind")
        self.assertEqual(command[index + 1], "/axeyum-vroot/cache")
        self.assertLess(index, command.index("/source"))
        self.assertLess(command.index("/source"), command.index("/target"))
        self.assertNotIn("/home/mjbommar/.cargo", command)
        self.assertEqual(command[-3:], ["--", "cargo", "rustc"])

    def test_local_result_and_inventory_are_both_replayed(self):
        with tempfile.TemporaryDirectory() as raw:
            envelope = Path(raw) / "cache-v5"
            cargo_home = envelope / "cargo-home"
            cargo_home.mkdir(parents=True)
            (cargo_home / "payload").write_bytes(b"cache\n")
            inventory = CAPTURE.V5.V4.inventory_cache(cargo_home)
            local = {
                "identity_sha256": "identity",
                "inventory": inventory,
                "probe": {"packages": 1},
                "status": "accepted",
                "summary": {"builds": 0},
                "upstream": {"commit": "source"},
            }
            result_path = envelope / "preparation-result.json"
            result_path.write_text(json.dumps(local), encoding="utf-8")
            committed = {
                **local,
                "local_result_sha256": CAPTURE.V1.sha256_file(result_path),
            }
            registration = {"cache_result": committed}
            with (
                mock.patch.object(CAPTURE, "LOCAL_CACHE_ENVELOPE", envelope),
                mock.patch.object(CAPTURE, "LOCAL_CACHE_HOME", cargo_home),
                mock.patch.object(CAPTURE, "LOCAL_CACHE_RESULT", result_path),
            ):
                self.assertEqual(CAPTURE.validate_local_cache(registration), inventory)
                original_result = result_path.read_text(encoding="utf-8")
                result_path.write_text(original_result + "\n", encoding="utf-8")
                self.assertEqual(
                    capture_error(lambda: CAPTURE.validate_local_cache(registration)),
                    ("cache", "local_result_hash"),
                )
                result_path.write_text(original_result, encoding="utf-8")
                (cargo_home / "payload").write_bytes(b"drift\n")
                self.assertEqual(
                    capture_error(lambda: CAPTURE.validate_local_cache(registration)),
                    ("cache", "inventory_drift"),
                )

    def test_cache_mount_cannot_be_writable_or_redirected(self):
        overlay = json.loads(CAPTURE.DEFAULT_REGISTRATION.read_text(encoding="utf-8"))
        CAPTURE.validate_registration(
            CAPTURE.read_registration(CAPTURE.DEFAULT_REGISTRATION)
        )
        for field, value in (("read_only", False), ("virtual", "/home/mjbommar/.cargo")):
            candidate = json.loads(json.dumps(overlay))
            candidate["cache_mount"][field] = value
            with tempfile.TemporaryDirectory() as raw:
                path = Path(raw) / "registration.json"
                path.write_text(json.dumps(candidate), encoding="utf-8")
                self.assertEqual(
                    capture_error(lambda: CAPTURE.read_registration(path)),
                    ("registration", "cache_mount"),
                )

        for field in ("base_registration", "cache_summary"):
            candidate = json.loads(json.dumps(overlay))
            candidate[field]["sha256"] = "0" * 64
            with tempfile.TemporaryDirectory() as raw:
                path = Path(raw) / "registration.json"
                path.write_text(json.dumps(candidate), encoding="utf-8")
                self.assertEqual(
                    capture_error(lambda: CAPTURE.read_registration(path)),
                    ("registration", field),
                )

    def test_cache_probe_and_post_probe_inventory_are_exact(self):
        registration = {"cache_result": {"probe": {"packages": 162}}}
        before = {"sha256": "inventory-before"}
        with (
            mock.patch.object(CAPTURE, "validate_local_cache", return_value=before),
            mock.patch.object(
                CAPTURE.V5,
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
            mock.patch.object(CAPTURE, "validate_local_cache", return_value=before),
            mock.patch.object(
                CAPTURE.V5,
                "structural_probe",
                return_value={"packages": 162},
            ),
            mock.patch.object(
                CAPTURE.V5.V4,
                "inventory_cache",
                return_value={"sha256": "inventory-after"},
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

    def test_module_rejects_physical_cache_and_counts_virtual_cache(self):
        with tempfile.TemporaryDirectory() as raw:
            cache = Path(raw) / "cargo-home"
            cache.mkdir()
            with mock.patch.object(CAPTURE, "LOCAL_CACHE_HOME", cache):
                paths = CAPTURE.reject_host_tokens(
                    b"prefix /axeyum-vroot/cache suffix", []
                )
                self.assertEqual(paths["virtual_cache_occurrences"], 1)
                self.assertEqual(
                    capture_error(
                        lambda: CAPTURE.reject_host_tokens(
                            f"prefix {cache} suffix".encode(), []
                        )
                    ),
                    ("identity", "host_path"),
                )

    def test_outer_staging_publishes_only_finalized_result(self):
        with tempfile.TemporaryDirectory(dir=ROOT / "target") as raw:
            output = Path(raw) / "capture"
            args = CAPTURE.parse_args(["--output", str(output)])

            def fake_capture(delegate_args):
                delegate_args.output.mkdir()
                module = b"prefix /axeyum-vroot/cache suffix\n"
                (delegate_args.output / "kernel.ll").write_bytes(module)
                paths = CAPTURE.V1.reject_host_tokens(module, [])
                result = {
                    "schema": CAPTURE.RESULT_SCHEMA,
                    "status": "accepted",
                    "upstream": {"authenticated_cache": CAPTURE.CACHE_INPUT_IDENTITY},
                    "module": {},
                    "targets": [],
                    "tools": {},
                    "admitter_sha256": "admitter",
                    "summary": {"builds": 2},
                    "observations": {"builds": [dict(paths), dict(paths)]},
                    "identity_sha256": "delegate-identity",
                }
                (delegate_args.output / "capture-result.json").write_text(
                    json.dumps(result, indent=2, sort_keys=True) + "\n",
                    encoding="utf-8",
                )
                return result

            with (
                mock.patch.object(CAPTURE, "read_registration", return_value={}),
                mock.patch.object(CAPTURE, "validate_registration"),
                mock.patch.object(CAPTURE, "validate_local_cache"),
                mock.patch.object(CAPTURE.V1, "run_capture", side_effect=fake_capture),
            ):
                result = CAPTURE.run_capture(args)
            self.assertTrue(output.is_dir())
            self.assertEqual(result["module"]["virtual_cache_occurrences"], 1)
            self.assertNotEqual(result["identity_sha256"], "delegate-identity")
            saved = json.loads(
                (output / "capture-result.json").read_text(encoding="utf-8")
            )
            self.assertEqual(saved, result)

    def test_outer_staging_is_removed_on_delegate_failure(self):
        with tempfile.TemporaryDirectory(dir=ROOT / "target") as raw:
            output = Path(raw) / "capture"
            delegate = output.with_name(f".{output.name}.delegate-{os.getpid()}")
            args = CAPTURE.parse_args(["--output", str(output)])

            def fail_capture(delegate_args):
                delegate_args.output.mkdir()
                (delegate_args.output / "partial").write_bytes(b"partial")
                raise CAPTURE.CaptureError("build", "cargo_rustc", "failed")

            with (
                mock.patch.object(CAPTURE, "read_registration", return_value={}),
                mock.patch.object(CAPTURE, "validate_registration"),
                mock.patch.object(CAPTURE, "validate_local_cache"),
                mock.patch.object(CAPTURE.V1, "run_capture", side_effect=fail_capture),
            ):
                self.assertEqual(
                    capture_error(lambda: CAPTURE.run_capture(args)),
                    ("build", "cargo_rustc"),
                )
            self.assertFalse(output.exists())
            self.assertFalse(delegate.exists())


if __name__ == "__main__":
    unittest.main()
