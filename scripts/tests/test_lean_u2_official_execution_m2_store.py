from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
import unittest
import xml.etree.ElementTree as ET
from pathlib import Path

from scripts import lean_u2_official_execution as BASE
from scripts import lean_u2_official_execution_m2 as M2
from scripts import lean_u2_official_execution_m2_store as STORE


ROOT = Path(__file__).resolve().parents[2]


def descriptor(path: str, payload: bytes) -> dict:
    return {"path": path, "bytes": len(payload), "sha256": BASE.sha256_bytes(payload)}


def junit_xml() -> bytes:
    case_ids = M2.selected_contract()["shard"]["case_ids"]
    suite = ET.Element(
        "testsuite",
        {
            "name": "M2",
            "tests": str(len(case_ids)),
            "failures": "0",
            "errors": "0",
            "skipped": "0",
            "time": "1.0",
        },
    )
    for case_id in case_ids:
        ET.SubElement(
            suite,
            "testcase",
            {"name": case_id, "classname": "CTest", "time": "0.01"},
        )
    return ET.tostring(suite, encoding="utf-8", xml_declaration=True)


def sealed_fixture(schema: str, fixture_id: str) -> dict:
    return BASE.seal(
        {"schema": schema, "id": fixture_id, "record_sha256": ""}, schema
    )


class M2StoreFixture:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.source = Path("/m2/source")
        self.toolchain = Path("/m2/toolchain")
        self.harness_root = Path("/m2/harness")
        self.spec = M2.build_spec(
            implementation_revision="1" * 40,
            source_root=self.source,
            toolchain_root=self.toolchain,
            harness_build=self.harness_root,
            junit_path=Path("/m2/attempt/test-results.xml"),
        )
        self.stdout = b"synthetic stdout\n"
        self.stderr = b""
        self.terminal = BASE.seal(
            {
                "schema": "axeyum-lean-u2-official-execution-m2-terminal-v1",
                "class": "exited",
                "exit_code": 0,
                "signal": None,
                "process": {
                    "watchdog_fired": False,
                    "direct_child_reaped": True,
                    "live_non_zombie_pids_after_cleanup": [],
                },
                "raw_outputs": [
                    descriptor("raw/stderr.bin", self.stderr),
                    descriptor("raw/stdout.bin", self.stdout),
                ],
                "record_sha256": "",
            },
            "axeyum-lean-u2-official-execution-m2-terminal-v1",
        )
        self.raw_junit = junit_xml()
        self.junit = M2.parse_junit(self.raw_junit, self.terminal)
        self.wrapper = M2.render_environment_wrapper(self.source, self.toolchain)
        self.ctest = M2.render_ctest_file(
            source_root=self.source,
            toolchain_root=self.toolchain,
            harness_root=self.harness_root,
        )
        self.discovery_payload = M2.synthetic_discovery(
            source_root=self.source,
            toolchain_root=self.toolchain,
            harness_root=self.harness_root,
        )
        self.raw_discovery = (
            json.dumps(self.discovery_payload, sort_keys=True, separators=(",", ":"))
            + "\n"
        ).encode()
        self.harness = M2.build_harness_record(
            source_root=self.source,
            toolchain_root=self.toolchain,
            harness_root=self.harness_root,
            discovery_payload=self.discovery_payload,
        )
        self.discovery = BASE.seal(
            {
                "schema": "axeyum-lean-u2-official-execution-m2-discovery-v1",
                "raw": descriptor("raw/discovery.json", self.raw_discovery),
                "normalized": self.harness["discovery"],
                "record_sha256": "",
            },
            "axeyum-lean-u2-official-execution-m2-discovery-v1",
        )
        self.generated_payloads = {}
        for relative in M2.declared_generated_paths():
            if relative == BASE.CTEST_SOURCE_PATHS[2]:
                continue
            self.generated_payloads[relative] = (
                self.wrapper
                if relative == "tests/with_stage1_test_env.sh"
                else relative.encode()
            )
        generated_rows = [
            {
                "path": relative,
                "kind": "file",
                "mode": 0o644,
                "bytes": len(payload),
                "sha256": BASE.sha256_bytes(payload),
                "target": None,
            }
            for relative, payload in sorted(self.generated_payloads.items())
        ]
        original_payload = b"source"
        original = [
            {
                "path": "tests/util.sh",
                "kind": "file",
                "mode": 0o644,
                "bytes": len(original_payload),
                "sha256": BASE.sha256_bytes(original_payload),
                "target": None,
            }
        ]
        self.post = M2.build_post_record(
            original_files=original,
            generated_files=generated_rows,
            junit=self.junit,
        )
        self.projection = M2.result_projection(self.junit, self.post)
        self.cases = M2.build_case_records(
            spec=self.spec,
            terminal=self.terminal,
            junit=self.junit,
            post=self.post,
        )

    def install(self) -> None:
        self.root.mkdir(mode=0o755)
        records = {
            "source.json": sealed_fixture("m2-test-source-v1", "source"),
            "toolchain.json": sealed_fixture("m2-test-toolchain-v1", "toolchain"),
            "tools.json": sealed_fixture("m2-test-tools-v1", "tools"),
            "platform.json": sealed_fixture("m2-test-platform-v1", "platform"),
            "lane.json": sealed_fixture("m2-test-lane-v1", "lane"),
            "run.json": sealed_fixture("m2-test-run-v1", "run"),
            "shard.json": sealed_fixture("m2-test-shard-v1", "shard"),
            "harness.json": self.harness,
            "discovery.json": self.discovery,
            "spec.json": self.spec,
            "prelaunch.json": sealed_fixture("m2-test-prelaunch-v1", "prelaunch"),
            "terminal.json": self.terminal,
            "junit.json": self.junit,
            "post.json": self.post,
            "projection.json": self.projection,
        }
        for relative, value in records.items():
            BASE.install_json(self.root, relative, value)
        for relative, payload in (
            ("raw/discovery.json", self.raw_discovery),
            ("raw/stdout.bin", self.stdout),
            ("raw/stderr.bin", self.stderr),
            ("raw/junit.xml", self.raw_junit),
            ("artifacts/with_stage1_test_env.sh", self.wrapper),
            ("artifacts/CTestTestfile.cmake", self.ctest),
        ):
            BASE.install_bytes(self.root, relative, payload)
        for relative, payload in self.generated_payloads.items():
            BASE.install_bytes(self.root, STORE.generated_path(relative), payload)
        for ordinal, record in enumerate(self.cases):
            BASE.install_json(self.root, STORE.case_path(ordinal), record)


class LeanU2OfficialExecutionM2StoreTests(unittest.TestCase):
    def new_fixture(self) -> tuple[tempfile.TemporaryDirectory, M2StoreFixture]:
        temporary = tempfile.TemporaryDirectory(prefix="axeyum-m2-store-")
        fixture = M2StoreFixture(Path(temporary.name) / "evidence")
        fixture.install()
        return temporary, fixture

    def test_complete_store_round_trip_is_exact_and_read_only(self) -> None:
        temporary, fixture = self.new_fixture()
        self.addCleanup(temporary.cleanup)
        bundle = STORE.validate_dependencies(fixture.root)
        self.assertEqual(len(bundle["cases"]), 64)
        completion = STORE.install_completion(fixture.root)
        validated = STORE.validate_complete_store(fixture.root)
        self.assertEqual(validated, completion)
        self.assertEqual(len(completion["case_records"]), 64)
        self.assertEqual(completion["credits"]["official_outcomes"], 64)
        self.assertEqual(completion["credits"]["parity_credit"], 0)
        self.assertTrue(
            all(
                (fixture.root / row["path"]).stat().st_mode & 0o777 == 0o444
                for row in completion["dependencies"]
            )
        )

    def test_missing_case_extra_path_and_completion_before_closure_reject(self) -> None:
        temporary, fixture = self.new_fixture()
        self.addCleanup(temporary.cleanup)
        (fixture.root / STORE.case_path(63)).unlink()
        with self.assertRaisesRegex(STORE.M2StoreError, "missing M2 evidence"):
            STORE.build_completion(fixture.root)

        temporary2, fixture2 = self.new_fixture()
        self.addCleanup(temporary2.cleanup)
        BASE.install_bytes(fixture2.root, "invented.bin", b"invented")
        with self.assertRaisesRegex(STORE.M2StoreError, "unexpected M2 evidence"):
            STORE.build_completion(fixture2.root)

        temporary_nested, fixture_nested = self.new_fixture()
        self.addCleanup(temporary_nested.cleanup)
        BASE.install_bytes(fixture_nested.root, "raw/invented.bin", b"invented")
        with self.assertRaisesRegex(STORE.M2StoreError, "namespace closure"):
            STORE.build_completion(fixture_nested.root)

        temporary3, fixture3 = self.new_fixture()
        self.addCleanup(temporary3.cleanup)
        STORE.install_completion(fixture3.root)
        with self.assertRaisesRegex(STORE.M2StoreError, "completion exists"):
            STORE.validate_dependencies(fixture3.root)

    def test_case_generated_raw_and_completion_mutations_reject(self) -> None:
        mutations = (
            (STORE.case_path(0), b"{}", "record"),
            (
                STORE.generated_path("tests/with_stage1_test_env.sh"),
                b"wrong wrapper",
                "generated artifact",
            ),
            ("raw/stdout.bin", b"wrong stdout", "raw-output"),
        )
        for relative, payload, message in mutations:
            temporary, fixture = self.new_fixture()
            self.addCleanup(temporary.cleanup)
            path = fixture.root / relative
            path.chmod(0o644)
            path.write_bytes(payload)
            path.chmod(0o444)
            with self.subTest(relative=relative):
                with self.assertRaisesRegex(STORE.M2StoreError, message):
                    STORE.build_completion(fixture.root)

        temporary, fixture = self.new_fixture()
        self.addCleanup(temporary.cleanup)
        STORE.install_completion(fixture.root)
        completion_path = fixture.root / "completion.json"
        changed = copy.deepcopy(BASE.load_canonical(completion_path))
        changed["dependencies"].pop()
        changed = BASE.seal(changed, STORE.COMPLETION_SCHEMA)
        completion_path.chmod(0o644)
        completion_path.write_bytes(BASE.canonical_bytes(changed))
        completion_path.chmod(0o444)
        with self.assertRaisesRegex(STORE.M2StoreError, "dependency closure"):
            STORE.validate_complete_store(fixture.root)

    def test_symlink_mutability_overwrite_and_cli_surface_reject(self) -> None:
        temporary, fixture = self.new_fixture()
        self.addCleanup(temporary.cleanup)
        raw = fixture.root / "raw/stdout.bin"
        raw.chmod(0o644)
        with self.assertRaisesRegex(STORE.M2StoreError, "mutable"):
            STORE.build_completion(fixture.root)

        temporary2, fixture2 = self.new_fixture()
        self.addCleanup(temporary2.cleanup)
        target = fixture2.root / "raw/stdout.bin"
        target.unlink()
        target.symlink_to("stderr.bin")
        with self.assertRaisesRegex(STORE.M2StoreError, "symlinked"):
            STORE.build_completion(fixture2.root)

        temporary3, fixture3 = self.new_fixture()
        self.addCleanup(temporary3.cleanup)
        with self.assertRaises(BASE.STORE.CheckpointConflict):
            BASE.install_bytes(fixture3.root, "raw/stdout.bin", b"different")

        result = subprocess.run(
            [sys.executable, str(Path(STORE.__file__).resolve()), "--help"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertNotIn(b"run-m2", result.stdout)


if __name__ == "__main__":
    unittest.main()
