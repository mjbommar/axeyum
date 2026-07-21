import copy
import importlib.util
import os
import sys
import tempfile
import unittest
from argparse import Namespace
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/prepare-tock-log2-cache-v3.py"
SPEC = importlib.util.spec_from_file_location("prepare_tock_log2_cache_v3", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
PREPARE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PREPARE
SPEC.loader.exec_module(PREPARE)


def capture_error(callable_):
    with unittest.TestCase().assertRaises(PREPARE.CaptureError) as raised:
        callable_()
    return raised.exception.stage, raised.exception.kind


class PrepareTockCacheV3Tests(unittest.TestCase):
    def registration(self, producer_hash):
        return {
            "schema": PREPARE.REGISTRATION_SCHEMA,
            "base_registration": PREPARE.BASE_REGISTRATION_IDENTITY,
            "upstream": {
                "commit": "ac5d597d22fbf3b03ef2169a577bac246ef65ffb",
                "tree": "5243357a7034d3a5fa68487ea839a25e573a25ef",
            },
            "environment": PREPARE.V2.EXPECTED_ENVIRONMENT,
            "fetch_args": PREPARE.V2.EXPECTED_FETCH_ARGS,
            "metadata_args": PREPARE.V2.EXPECTED_METADATA_ARGS,
            "dns_args": PREPARE.EXPECTED_DNS_ARGS,
            "resource_scope": PREPARE.SUPPORT.EXPECTED_RESOURCE_SCOPE,
            "resolver": PREPARE.RESOLVER_IDENTITY,
            "namespace": {
                "network_root_argv": PREPARE.EXPECTED_NETWORK_ROOT,
                "offline_root_argv": PREPARE.V2.EXPECTED_OFFLINE_ROOT,
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

    def test_registration_freezes_resolver_dns_and_network_root(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            producer = root / "producer.py"
            producer.write_bytes(b"producer\n")
            base = self.registration(PREPARE.SUPPORT.sha256_file(producer))
            with mock.patch.object(PREPARE, "REPO", root):
                PREPARE.validate_registration(base)
                mutations = [
                    lambda row: row["resolver"].__setitem__("sha256", "0" * 64),
                    lambda row: row["dns_args"].__setitem__(1, "example.com"),
                    lambda row: row["namespace"]["network_root_argv"].remove(
                        str(PREPARE.RESOLVER_PATH)
                    ),
                    lambda row: row["namespace"]["offline_root_argv"].append(
                        str(PREPARE.RESOLVER_PATH)
                    ),
                    lambda row: row["tools"].pop("getent"),
                    lambda row: row["producer_files"][0].__setitem__(
                        "sha256", "f" * 64
                    ),
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

    def test_resolver_hash_mode_and_size_are_checked(self):
        with tempfile.TemporaryDirectory() as raw:
            resolver = Path(raw) / "resolv.conf"
            payload = b"nameserver 127.0.0.53\n"
            resolver.write_bytes(payload)
            resolver.chmod(0o644)
            identity = {
                "path": str(resolver),
                "sha256": PREPARE.SUPPORT.sha256_file(resolver),
                "mode": 0o644,
                "size": len(payload),
            }
            with (
                mock.patch.object(PREPARE, "RESOLVER_PATH", resolver),
                mock.patch.object(PREPARE, "RESOLVER_IDENTITY", identity),
            ):
                PREPARE.validate_resolver()
                resolver.chmod(0o600)
                self.assertEqual(
                    capture_error(PREPARE.validate_resolver), ("resolver", "mode")
                )
                resolver.chmod(0o644)
                resolver.write_bytes(payload + b"search example\n")
                self.assertEqual(
                    capture_error(PREPARE.validate_resolver), ("resolver", "size")
                )

    def test_network_namespace_binds_exact_resolver_and_offline_does_not(self):
        registration = {"tools": {"bwrap": {"path": "/usr/bin/bwrap"}}}
        network = PREPARE.network_namespace_command(
            registration,
            source=Path("/source"),
            cache=Path("/cache"),
            target=Path("/target"),
            child=["/usr/bin/getent", *PREPARE.EXPECTED_DNS_ARGS],
        )
        resolver = str(PREPARE.RESOLVER_PATH)
        self.assertEqual(network.count(resolver), 2)
        first = network.index(resolver)
        self.assertEqual(network[first - 1], "--ro-bind")
        self.assertEqual(
            network[-4:], ["--", "/usr/bin/getent", "ahostsv4", "github.com"]
        )
        self.assertNotIn(resolver, PREPARE.V2.EXPECTED_OFFLINE_ROOT)

    def test_dns_output_requires_only_valid_ipv4_rows(self):
        output = (
            "140.82.112.3 STREAM github.com\n"
            "140.82.112.3 DGRAM\n"
            "140.82.113.3 RAW\n"
        )
        self.assertEqual(
            PREPARE.parse_dns_output(output), ["140.82.112.3", "140.82.113.3"]
        )
        self.assertEqual(
            capture_error(lambda: PREPARE.parse_dns_output("")), ("dns", "empty")
        )
        self.assertEqual(
            capture_error(lambda: PREPARE.parse_dns_output("not-an-ip STREAM\n")),
            ("dns", "output"),
        )
        self.assertEqual(
            capture_error(lambda: PREPARE.parse_dns_output("::1 STREAM\n")),
            ("dns", "output"),
        )

    def test_dns_failure_removes_partial_output(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            output = root / "target/tock-log2-20260721/cache-v3"
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
                mock.patch.object(PREPARE.V2, "reject_ambient_environment"),
                mock.patch.object(PREPARE, "validate_resolver"),
                mock.patch.object(PREPARE.SUPPORT, "validate_source_repo"),
                mock.patch.object(PREPARE.SUPPORT, "resource_snapshot", return_value=resource),
                mock.patch.object(PREPARE.SUPPORT, "materialize", side_effect=materialize),
                mock.patch.object(PREPARE.V2, "lock_package_count", return_value=169),
                mock.patch.object(
                    PREPARE,
                    "dns_probe",
                    side_effect=PREPARE.CaptureError("dns", "getent", "failed"),
                ),
            ):
                args = Namespace(
                    registration=root / "registration.json",
                    tock_repo=root / "tock",
                    output=output,
                )
                self.assertEqual(
                    capture_error(lambda: PREPARE.run_preparation(args)),
                    ("dns", "getent"),
                )
            self.assertFalse(output.exists())
            self.assertEqual(list(output.parent.glob(".cache-v3.partial-*")), [])


if __name__ == "__main__":
    unittest.main()
