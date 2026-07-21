import copy
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/prepare-tock-log2-cache-v5.py"
SPEC = importlib.util.spec_from_file_location("prepare_tock_log2_cache_v5", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
PREPARE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PREPARE
SPEC.loader.exec_module(PREPARE)


def capture_error(callable_):
    with unittest.TestCase().assertRaises(PREPARE.CaptureError) as raised:
        callable_()
    return raised.exception.stage, raised.exception.kind


class PrepareTockCacheV5Tests(unittest.TestCase):
    def write_source(self, root):
        (root / "kernel").mkdir()
        (root / "kernel/Cargo.toml").write_text("[package]\nname='kernel'\nversion='1.0.0'\n")
        (root / "Cargo.lock").write_text(
            """version = 4

[[package]]
name = "inactive"
version = "9.0.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

[[package]]
name = "kernel"
version = "1.0.0"

[[package]]
name = "serde"
version = "1.0.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
""",
            encoding="utf-8",
        )

    def metadata(self):
        kernel_id = "path+file:///axeyum-vroot/source/kernel#1.0.0"
        serde_id = "registry+https://github.com/rust-lang/crates.io-index#serde@1.0.0"
        return {
            "workspace_root": "/axeyum-vroot/source",
            "workspace_members": [kernel_id],
            "workspace_default_members": [kernel_id],
            "packages": [
                {
                    "id": serde_id,
                    "name": "serde",
                    "version": "1.0.0",
                    "source": "registry+https://github.com/rust-lang/crates.io-index",
                    "manifest_path": "/axeyum-vroot/cache/registry/src/serde/Cargo.toml",
                },
                {
                    "id": kernel_id,
                    "name": "kernel",
                    "version": "1.0.0",
                    "source": None,
                    "manifest_path": "/axeyum-vroot/source/kernel/Cargo.toml",
                },
            ],
            "resolve": {
                "nodes": [
                    {
                        "id": serde_id,
                        "dependencies": [],
                        "deps": [],
                    },
                    {
                        "id": kernel_id,
                        "dependencies": [serde_id],
                        "deps": [{"name": "serde", "pkg": serde_id}],
                    },
                ]
            },
        }

    def run_probe(self, source, metadata, expected=3):
        completed = mock.Mock(returncode=0, stdout=json.dumps(metadata), stderr="")
        registration = {
            "tools": {
                "bwrap": {"path": "/usr/bin/bwrap"},
                "cargo": {"path": "/cargo"},
            },
            "expected_lock_packages": expected,
        }
        with mock.patch.object(PREPARE.SUPPORT, "command", return_value=completed):
            return PREPARE.structural_probe(
                registration, source, Path("/cache"), Path("/target")
            )

    def test_inactive_lock_entry_is_allowed_and_count_is_result_only(self):
        with tempfile.TemporaryDirectory() as raw:
            source = Path(raw)
            self.write_source(source)
            result = self.run_probe(source, self.metadata())
            self.assertEqual(result["lock_packages"], 3)
            self.assertEqual(result["packages"], 2)
            self.assertEqual(result["nodes"], 2)
            self.assertEqual(result["kernel_packages"], 1)
            self.assertEqual(len(result["active_resolution_sha256"]), 64)
            reordered = self.metadata()
            reordered["packages"].reverse()
            reordered["resolve"]["nodes"].reverse()
            self.assertEqual(
                self.run_probe(source, reordered)["active_resolution_sha256"],
                result["active_resolution_sha256"],
            )

    def test_unknown_dependency_and_node_set_drift_fail(self):
        with tempfile.TemporaryDirectory() as raw:
            source = Path(raw)
            self.write_source(source)
            unknown = self.metadata()
            unknown["resolve"]["nodes"][1]["dependencies"] = ["unknown"]
            self.assertEqual(
                capture_error(lambda: self.run_probe(source, unknown)),
                ("probe", "unknown_dependency"),
            )
            missing_node = self.metadata()
            missing_node["resolve"]["nodes"].pop()
            self.assertEqual(
                capture_error(lambda: self.run_probe(source, missing_node)),
                ("probe", "node_package_set"),
            )

    def test_lock_source_checksum_and_manifest_are_authenticated(self):
        with tempfile.TemporaryDirectory() as raw:
            source = Path(raw)
            self.write_source(source)
            wrong_source = self.metadata()
            wrong_source["packages"][0]["source"] = "registry+https://example.invalid/index"
            self.assertEqual(
                capture_error(lambda: self.run_probe(source, wrong_source)),
                ("probe", "package_not_locked"),
            )
            escaped = self.metadata()
            escaped["packages"][1]["manifest_path"] = "/outside/Cargo.toml"
            self.assertEqual(
                capture_error(lambda: self.run_probe(source, escaped)),
                ("probe", "manifest_escape"),
            )
            (source / "Cargo.lock").write_text(
                (source / "Cargo.lock").read_text().replace("b" * 64, "short"),
                encoding="utf-8",
            )
            self.assertEqual(
                capture_error(lambda: self.run_probe(source, self.metadata())),
                ("probe", "registry_checksum"),
            )

    def test_workspace_and_kernel_invariants_fail_precisely(self):
        with tempfile.TemporaryDirectory() as raw:
            source = Path(raw)
            self.write_source(source)
            default_drift = self.metadata()
            default_drift["workspace_default_members"] = [
                default_drift["packages"][0]["id"]
            ]
            self.assertEqual(
                capture_error(lambda: self.run_probe(source, default_drift)),
                ("probe", "default_not_workspace"),
            )
            no_kernel = self.metadata()
            no_kernel["packages"][1]["name"] = "not-kernel"
            self.assertEqual(
                capture_error(lambda: self.run_probe(source, no_kernel)),
                ("probe", "package_not_locked"),
            )

    def test_duplicate_lock_identity_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            source = Path(raw)
            self.write_source(source)
            lock = (source / "Cargo.lock").read_text(encoding="utf-8")
            duplicate = lock[lock.index("[[package]]\nname = \"kernel\"") :]
            duplicate = duplicate[: duplicate.index("\n\n[[package]]", 1)]
            (source / "Cargo.lock").write_text(lock + "\n" + duplicate + "\n", encoding="utf-8")
            self.assertEqual(
                capture_error(lambda: self.run_probe(source, self.metadata(), expected=4)),
                ("probe", "duplicate_lock_identity"),
            )


if __name__ == "__main__":
    unittest.main()
