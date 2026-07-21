import copy
import importlib.util
import json
import os
import stat
import sys
import tempfile
import unittest
from argparse import Namespace
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/prepare-tock-log2-cache-v2.py"
SPEC = importlib.util.spec_from_file_location("prepare_tock_log2_cache_v2", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
PREPARE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PREPARE
SPEC.loader.exec_module(PREPARE)


def capture_error(callable_):
    with unittest.TestCase().assertRaises(PREPARE.CaptureError) as raised:
        callable_()
    return raised.exception.stage, raised.exception.kind


class PrepareTockCacheV2Tests(unittest.TestCase):
    def registration(self, producer_hash):
        return {
            "schema": PREPARE.REGISTRATION_SCHEMA,
            "upstream": {
                "commit": "ac5d597d22fbf3b03ef2169a577bac246ef65ffb",
                "tree": "5243357a7034d3a5fa68487ea839a25e573a25ef",
            },
            "environment": PREPARE.EXPECTED_ENVIRONMENT,
            "fetch_args": PREPARE.EXPECTED_FETCH_ARGS,
            "metadata_args": PREPARE.EXPECTED_METADATA_ARGS,
            "resource_scope": PREPARE.SUPPORT.EXPECTED_RESOURCE_SCOPE,
            "namespace": {
                "network_root_argv": PREPARE.EXPECTED_NETWORK_ROOT,
                "offline_root_argv": PREPARE.EXPECTED_OFFLINE_ROOT,
                "source": "/axeyum-vroot/source",
                "cache": "/axeyum-vroot/cache",
                "target": "/axeyum-vroot/target",
                "cwd": "/axeyum-vroot/source",
            },
            "tools": {name: {} for name in PREPARE.EXPECTED_TOOLS},
            "critical_files": [{"path": "Cargo.lock", "sha256": "0" * 64}],
            "producer_files": [
                {"path": "producer.py", "sha256": producer_hash},
            ],
            "expected_lock_packages": 169,
        }

    def test_registration_freezes_commands_namespace_and_producer(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            producer = root / "producer.py"
            producer.write_bytes(b"producer\n")
            base = self.registration(PREPARE.sha256_file(producer))
            with mock.patch.object(PREPARE, "REPO", root):
                PREPARE.validate_registration(base)
                mutations = [
                    lambda row: row.__setitem__("schema", "wrong"),
                    lambda row: row["upstream"].__setitem__("tree", "0" * 40),
                    lambda row: row["environment"].append(["HTTP_PROXY", "x"]),
                    lambda row: row["fetch_args"].append("--offline"),
                    lambda row: row["metadata_args"].remove("--offline"),
                    lambda row: row["resource_scope"].__setitem__(
                        "memory_max_bytes", 1
                    ),
                    lambda row: row["namespace"].__setitem__(
                        "cache", "/different"
                    ),
                    lambda row: row["tools"].pop("cargo"),
                    lambda row: row["producer_files"][0].__setitem__(
                        "sha256", "f" * 64
                    ),
                    lambda row: row.__setitem__("expected_lock_packages", 168),
                ]
                for index, mutate in enumerate(mutations):
                    with self.subTest(index=index):
                        candidate = copy.deepcopy(base)
                        mutate(candidate)
                        self.assertEqual(
                            capture_error(
                                lambda candidate=candidate: PREPARE.validate_registration(
                                    candidate
                                )
                            )[0],
                            "registration",
                        )

    def test_ambient_overrides_are_rejected(self):
        PREPARE.reject_ambient_environment({"PATH": "/bin", "GIT_PAGER": "cat"})
        for name in [
            "RUSTFLAGS",
            "HTTPS_PROXY",
            "CARGO_REGISTRIES_CRATES_IO_INDEX",
            "CARGO_NET_OFFLINE",
            "RUSTC_WRAPPER",
        ]:
            with self.subTest(name=name):
                self.assertEqual(
                    capture_error(
                        lambda name=name: PREPARE.reject_ambient_environment(
                            {name: "injected"}
                        )
                    ),
                    ("environment", "ambient_override"),
                )

    def test_network_and_offline_namespace_differ_only_as_registered(self):
        registration = {"tools": {"bwrap": {"path": "/usr/bin/bwrap"}}}
        source = Path("/physical/source")
        cache = Path("/physical/cache")
        target = Path("/physical/target")
        network = PREPARE.namespace_command(
            registration,
            network=True,
            source=source,
            cache=cache,
            target=target,
            child=["cargo", "fetch"],
        )
        offline = PREPARE.namespace_command(
            registration,
            network=False,
            source=source,
            cache=cache,
            target=target,
            child=["cargo", "metadata"],
        )
        self.assertEqual(network.count("--share-net"), 1)
        self.assertNotIn("--share-net", offline)
        self.assertIn("--bind", network)
        cache_index = network.index(str(cache))
        self.assertEqual(network[cache_index - 1], "--bind")
        offline_cache_index = offline.index(str(cache))
        self.assertEqual(offline[offline_cache_index - 1], "--ro-bind")
        self.assertEqual(network.count("cargo"), 1)
        self.assertEqual(offline.count("cargo"), 1)

    def test_lock_package_count_is_exact(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "Cargo.lock").write_text(
                "[[package]]\nname='a'\n[[package]]\nname='b'\n", encoding="utf-8"
            )
            self.assertEqual(PREPARE.lock_package_count(root), 2)

    def test_inventory_is_canonical_and_counts_payload(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package = root / "registry/src/index/crate-1.0.0"
            package.mkdir(parents=True)
            payload = package / "lib.rs"
            payload.write_bytes(b"pub fn value() -> u8 { 1 }\n")
            checkout = root / "git/checkouts/repo/abcdef0"
            checkout.mkdir(parents=True)
            (checkout / "README").write_bytes(b"readme\n")
            (root / "relative-link").symlink_to("registry/src")
            first = PREPARE.inventory_cache(root)
            second = PREPARE.inventory_cache(root)
            self.assertEqual(first, second)
            self.assertEqual(first["registry_packages"], 1)
            self.assertEqual(first["git_checkouts"], 1)
            self.assertEqual(first["files"], 2)
            payload.write_bytes(b"pub fn value() -> u8 { 2 }\n")
            self.assertNotEqual(PREPARE.inventory_cache(root)["sha256"], first["sha256"])

    def test_inventory_rejects_hardlinks_symlink_escape_temp_and_fifo(self):
        cases = []
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            original = root / "original"
            original.write_bytes(b"x")
            os.link(original, root / "alias")
            cases.append((root, ("inventory", "hardlink")))
            self.assertEqual(capture_error(lambda: PREPARE.inventory_cache(root)), cases[-1][1])

        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "escape").symlink_to("../outside")
            self.assertEqual(
                capture_error(lambda: PREPARE.inventory_cache(root)),
                ("inventory", "escaping_symlink"),
            )

        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "download.part").write_bytes(b"partial")
            self.assertEqual(
                capture_error(lambda: PREPARE.inventory_cache(root)),
                ("inventory", "temporary_path"),
            )

        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            fifo = root / "fifo"
            os.mkfifo(fifo)
            self.assertTrue(stat.S_ISFIFO(fifo.lstat().st_mode))
            self.assertEqual(
                capture_error(lambda: PREPARE.inventory_cache(root)),
                ("inventory", "special_file"),
            )

    def test_offline_probe_checks_workspace_kernel_and_package_count(self):
        metadata = {
            "workspace_root": "/axeyum-vroot/source",
            "packages": [{"name": "kernel"}, *({"name": f"p{index}"} for index in range(168))],
        }
        completed = mock.Mock(returncode=0, stdout=json.dumps(metadata), stderr="")
        registration = {
            "tools": {
                "bwrap": {"path": "/usr/bin/bwrap"},
                "cargo": {"path": "/cargo"},
            },
            "expected_lock_packages": 169,
        }
        with mock.patch.object(PREPARE, "command", return_value=completed):
            result = PREPARE.offline_probe(
                registration, Path("/source"), Path("/cache"), Path("/target")
            )
            self.assertEqual(result, {"packages": 169, "kernel_packages": 1})
            registration["expected_lock_packages"] = 170
            self.assertEqual(
                capture_error(
                    lambda: PREPARE.offline_probe(
                        registration,
                        Path("/source"),
                        Path("/cache"),
                        Path("/target"),
                    )
                ),
                ("probe", "package_count"),
            )

    def test_identity_excludes_only_observations_and_digest(self):
        result = {
            "stable": 1,
            "observations": {"wall_ms": 2},
            "identity_sha256": "digest",
        }
        self.assertEqual(PREPARE.identity_projection(result), {"stable": 1})

    def test_fetch_failure_removes_partial_output(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            output = root / "target/tock-log2-20260721/cache-v2"
            registration = {"tools": {}, "expected_lock_packages": 169}
            resource = {
                "cgroup": "/scope",
                "memory_high_bytes": PREPARE.SUPPORT.EXPECTED_MEMORY_HIGH,
                "memory_max_bytes": PREPARE.SUPPORT.EXPECTED_MEMORY_MAX,
                "swap_max_bytes": PREPARE.SUPPORT.EXPECTED_SWAP_MAX,
                "events": {"oom": 0, "oom_kill": 0, "oom_group_kill": 0},
            }

            def materialize(_repo, destination, _registration):
                destination.mkdir()

            with (
                mock.patch.object(PREPARE, "REPO", root),
                mock.patch.object(PREPARE, "read_registration", return_value=registration),
                mock.patch.object(PREPARE, "validate_registration"),
                mock.patch.object(PREPARE, "reject_ambient_environment"),
                mock.patch.object(PREPARE.SUPPORT, "validate_source_repo"),
                mock.patch.object(PREPARE.SUPPORT, "resource_snapshot", return_value=resource),
                mock.patch.object(PREPARE.SUPPORT, "materialize", side_effect=materialize),
                mock.patch.object(PREPARE, "lock_package_count", return_value=169),
                mock.patch.object(
                    PREPARE,
                    "run_fetch",
                    side_effect=PREPARE.CaptureError("fetch", "cargo_fetch", "failed"),
                ),
            ):
                args = Namespace(
                    registration=root / "registration.json",
                    tock_repo=root / "tock",
                    output=output,
                )
                self.assertEqual(
                    capture_error(lambda: PREPARE.run_preparation(args)),
                    ("fetch", "cargo_fetch"),
                )
            self.assertFalse(output.exists())
            self.assertEqual(list(output.parent.glob(".cache-v2.partial-*")), [])


if __name__ == "__main__":
    unittest.main()
