from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import lean_u2_official_execution as BASE
from scripts import lean_u2_official_execution_m2 as M2
from scripts import lean_u2_official_execution_m2_run as RUN


ROOT = Path(__file__).resolve().parents[2]


class FakeProcess:
    def __init__(self, returncode: int, stdout: object, stderr: object) -> None:
        self.returncode = returncode
        self.pid = 987_654_321
        stdout.write(b"synthetic ctest stdout\n")
        stderr.write(b"")

    def poll(self) -> int:
        return self.returncode

    def wait(self, timeout: float) -> int:
        return self.returncode


class LeanU2OfficialExecutionM2RunTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="axeyum-m2-run-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        (self.source / "tests").mkdir(parents=True)
        self.toolchain = self.root / "toolchain"
        self.toolchain.mkdir()
        self.harness = self.root / "harness"

    def spec(self) -> dict:
        return M2.build_spec(
            implementation_revision="1" * 40,
            source_root=self.source,
            toolchain_root=self.toolchain,
            harness_build=self.harness,
            junit_path=self.root / "attempt/test-results.xml",
        )

    @staticmethod
    def manifest_file(path: str, sha256: str = "0" * 64) -> dict:
        return {
            "path": path,
            "kind": "file",
            "mode": 0o644,
            "bytes": 1,
            "sha256": sha256,
            "target": None,
        }

    def selected_source(self) -> dict:
        rows = {}
        for case in M2.selected_contract()["cases"]:
            rows[case["source_path"]] = self.manifest_file(
                case["source_path"], case["source_sha256"]
            )
            for sidecar in case["sidecars"]:
                rows[sidecar] = self.manifest_file(sidecar)
            runner = case["registration"]["command"][2].removeprefix(
                "$LEAN_ROOT/"
            )
            rows[runner] = self.manifest_file(runner)
        rows[RUN.COMPILE_BENCH_RUNNER_PATH] = copy.deepcopy(
            RUN.COMPILE_BENCH_RUNNER_ROW
        )
        rows[RUN.COMPILE_RUNNER_TARGET_PATH] = copy.deepcopy(
            RUN.COMPILE_RUNNER_TARGET_ROW
        )
        return {"files": sorted(rows.values(), key=lambda row: row["path"])}

    def prepare(self) -> tuple[dict, dict, bytes, bytes, bytes]:
        payload = M2.synthetic_discovery(
            source_root=self.source,
            toolchain_root=self.toolchain,
            harness_root=self.harness,
        )

        def fake_run(command: list[str], **kwargs: object) -> subprocess.CompletedProcess:
            self.assertEqual(
                command,
                [
                    "/usr/bin/ctest",
                    "--test-dir",
                    str(self.harness),
                    "--show-only=json-v1",
                    "-E",
                    "foreign",
                ],
            )
            self.assertEqual(kwargs["cwd"], self.source)
            return subprocess.CompletedProcess(
                command,
                0,
                stdout=json.dumps(payload).encode(),
                stderr=b"",
            )

        return RUN.prepare_harness(
            source_root=self.source,
            toolchain_root=self.toolchain,
            harness_root=self.harness,
            run_command=fake_run,
        )

    def test_harness_discovery_and_records_are_exact(self) -> None:
        harness, discovery, wrapper, ctest, raw = self.prepare()
        self.assertTrue(BASE.valid_seal(harness, M2.HARNESS_SCHEMA))
        self.assertEqual(len(discovery["normalized"]), 64)
        self.assertEqual(discovery["raw"]["sha256"], BASE.sha256_bytes(raw))
        self.assertEqual(harness["wrapper"]["sha256"], BASE.sha256_bytes(wrapper))
        self.assertEqual(harness["ctest_file"]["sha256"], BASE.sha256_bytes(ctest))
        self.assertEqual(
            RUN.validate_discovery_record(
                discovery,
                spec=self.spec(),
                harness=harness,
                raw=raw,
            ),
            [],
        )
        lane = RUN.build_lane_record()
        shard = RUN.build_shard_record()
        self.assertEqual(RUN.validate_lane_record(lane), [])
        self.assertEqual(RUN.validate_shard_record(shard), [])
        changed = copy.deepcopy(shard)
        changed["parent_completed"] = True
        changed = BASE.seal(changed, RUN.SHARD_SCHEMA)
        self.assertTrue(RUN.validate_shard_record(changed))

    def test_discovery_mutations_reject_before_process(self) -> None:
        payload = M2.synthetic_discovery(
            source_root=self.source,
            toolchain_root=self.toolchain,
            harness_root=self.harness,
        )
        payload["tests"][0]["properties"][0]["value"] = "/wrong"

        def fake_run(command: list[str], **kwargs: object) -> subprocess.CompletedProcess:
            return subprocess.CompletedProcess(
                command, 0, stdout=json.dumps(payload).encode(), stderr=b""
            )

        with self.assertRaisesRegex(RUN.M2RunError, "discovery row"):
            RUN.prepare_harness(
                source_root=self.source,
                toolchain_root=self.toolchain,
                harness_root=self.harness,
                run_command=fake_run,
            )

    def test_run_and_prelaunch_link_every_identity(self) -> None:
        harness, discovery, _, _, _ = self.prepare()
        spec = self.spec()
        source = BASE.seal(
            {"schema": "m2-test-source-v1", "record_sha256": ""},
            "m2-test-source-v1",
        )
        toolchain = BASE.seal(
            {"schema": "m2-test-toolchain-v1", "record_sha256": ""},
            "m2-test-toolchain-v1",
        )
        tools = BASE.seal(
            {"schema": "m2-test-tools-v1", "record_sha256": ""},
            "m2-test-tools-v1",
        )
        platform = BASE.seal(
            {
                "schema": RUN.PLATFORM_SCHEMA,
                "captured_utc": "2026-07-22T00:00:00Z",
                "platform": {"provider": "local-process"},
                "uname": ["a", "b", "c", "d", "e"],
                "glibc": "glibc 2",
                "online_cpu_count": 1,
                "official_provider_claimed": False,
                "record_sha256": "",
            },
            RUN.PLATFORM_SCHEMA,
        )
        lane = RUN.build_lane_record()
        shard = RUN.build_shard_record()
        storage = BASE.STORE.capture_storage_class(BASE.STORE.STORAGE_CLASS_IDS[0], ROOT)
        run = RUN.build_run_record(
            spec=spec,
            source=source,
            toolchain=toolchain,
            tools=tools,
            platform=platform,
            lane=lane,
            shard=shard,
            harness=harness,
            discovery=discovery,
            storage=storage,
        )
        self.assertEqual(
            RUN.validate_run_record(
                run,
                spec=spec,
                source=source,
                toolchain=toolchain,
                tools=tools,
                platform=platform,
                lane=lane,
                shard=shard,
                harness=harness,
                discovery=discovery,
            ),
            [],
        )
        prelaunch = RUN.build_prelaunch_record(spec=spec, run=run, shard=shard)
        self.assertEqual(
            RUN.validate_prelaunch_record(
                prelaunch, spec=spec, run=run, shard=shard
            ),
            [],
        )
        changed = copy.deepcopy(prelaunch)
        changed["selection_case_ids"] = list(reversed(changed["selection_case_ids"]))
        changed = BASE.seal(changed, RUN.PRELAUNCH_SCHEMA)
        self.assertTrue(
            RUN.validate_prelaunch_record(
                changed, spec=spec, run=run, shard=shard
            )
        )

    def test_process_adapter_classifies_exit_and_launch_failure_offline(self) -> None:
        self.harness.mkdir()
        spec = self.spec()
        prelaunch = BASE.seal(
            {"schema": "m2-test-prelaunch-v1", "record_sha256": ""},
            "m2-test-prelaunch-v1",
        )

        def factory(command: list[str], **kwargs: object) -> FakeProcess:
            return FakeProcess(0, kwargs["stdout"], kwargs["stderr"])

        terminal, stdout, stderr = RUN.execute_process(
            spec,
            self.root / "attempt-exit",
            prelaunch["record_sha256"],
            popen_factory=factory,
            live_members=lambda _pgid: [],
            sample_rss=lambda _pid: 1234,
        )
        self.assertEqual(terminal["class"], "exited")
        self.assertEqual(terminal["exit_code"], 0)
        self.assertEqual(
            RUN.validate_terminal_record(
                terminal,
                prelaunch=prelaunch,
                stdout=stdout,
                stderr=stderr,
                require_eligible=True,
            ),
            [],
        )
        changed = copy.deepcopy(terminal)
        changed["wall_time"]["value"] = -1
        changed = BASE.seal(changed, RUN.TERMINAL_SCHEMA)
        self.assertTrue(
            RUN.validate_terminal_record(
                changed,
                prelaunch=prelaunch,
                stdout=stdout,
                stderr=stderr,
                require_eligible=True,
            )
        )
        changed = copy.deepcopy(terminal)
        changed["exit_code"] = 7
        changed = BASE.seal(changed, RUN.TERMINAL_SCHEMA)
        self.assertTrue(
            RUN.validate_terminal_record(
                changed,
                prelaunch=prelaunch,
                stdout=stdout,
                stderr=stderr,
                require_eligible=True,
            )
        )

        def launch_failure(command: list[str], **kwargs: object) -> FakeProcess:
            raise OSError(2, "synthetic missing executable")

        failed, failed_stdout, failed_stderr = RUN.execute_process(
            spec,
            self.root / "attempt-launch-failed",
            prelaunch["record_sha256"],
            popen_factory=launch_failure,
            live_members=lambda _pgid: [],
            sample_rss=lambda _pid: None,
        )
        self.assertEqual(failed["class"], "launch-failed")
        self.assertTrue(
            RUN.validate_terminal_record(
                failed,
                prelaunch=prelaunch,
                stdout=failed_stdout,
                stderr=failed_stderr,
                require_eligible=True,
            )
        )

    def test_selected_source_and_cli_fail_closed_without_live_run(self) -> None:
        source = self.selected_source()
        with mock.patch.object(BASE, "validate_source_record", return_value=[]):
            self.assertEqual(RUN.validate_selected_source(source), [])
            compile_bench = [
                case
                for case in M2.selected_contract()["cases"]
                if case["registration"]["command"][2]
                == "$LEAN_ROOT/" + RUN.COMPILE_BENCH_RUNNER_PATH
            ]
            self.assertEqual(len(compile_bench), 24)
            changed = copy.deepcopy(source)
            target = next(
                row
                for row in changed["files"]
                if row["path"] == M2.selected_contract()["cases"][0]["source_path"]
            )
            target["sha256"] = "f" * 64
            self.assertTrue(RUN.validate_selected_source(changed))

        checked = subprocess.run(
            [sys.executable, str(Path(RUN.__file__).resolve()), "offline-check"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(checked.returncode, 0, checked.stderr.decode())
        self.assertIn(
            b"run_command=true|live_execution_observed=false|outcomes=0|parity=0",
            checked.stdout,
        )
        help_result = subprocess.run(
            [sys.executable, str(Path(RUN.__file__).resolve()), "--help"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(help_result.returncode, 0, help_result.stderr.decode())
        self.assertIn(b"run-m2", help_result.stdout)

    def test_compile_bench_runner_symlink_mutations_fail_closed(self) -> None:
        source = self.selected_source()

        def mutate_row(value: dict, path: str) -> dict:
            return next(row for row in value["files"] if row["path"] == path)

        mutations = {}

        missing = copy.deepcopy(source)
        missing["files"] = [
            row
            for row in missing["files"]
            if row["path"] != RUN.COMPILE_BENCH_RUNNER_PATH
        ]
        mutations["missing"] = missing

        renamed = copy.deepcopy(source)
        mutate_row(renamed, RUN.COMPILE_BENCH_RUNNER_PATH)["path"] += ".renamed"
        mutations["renamed"] = renamed

        regularized = copy.deepcopy(source)
        link = mutate_row(regularized, RUN.COMPILE_BENCH_RUNNER_PATH)
        link.update(self.manifest_file(RUN.COMPILE_BENCH_RUNNER_PATH))
        mutations["regularized"] = regularized

        for name, target in (
            ("absolute", "/tests/compile/run_test.sh"),
            ("escaping", "../../../outside/run_test.sh"),
            ("wrong-target", "../compiler/run_test.sh"),
        ):
            changed = copy.deepcopy(source)
            mutate_row(changed, RUN.COMPILE_BENCH_RUNNER_PATH)["target"] = target
            mutations[name] = changed

        chained = copy.deepcopy(source)
        target = mutate_row(chained, RUN.COMPILE_RUNNER_TARGET_PATH)
        target["kind"] = "symlink"
        target["target"] = "other.sh"
        mutations["chained"] = chained

        for field, value in (
            ("mode", 0o755),
            ("bytes", 21),
            ("sha256", "f" * 64),
        ):
            changed = copy.deepcopy(source)
            mutate_row(changed, RUN.COMPILE_BENCH_RUNNER_PATH)[field] = value
            mutations[f"link-{field}"] = changed

        target_missing = copy.deepcopy(source)
        target_missing["files"] = [
            row
            for row in target_missing["files"]
            if row["path"] != RUN.COMPILE_RUNNER_TARGET_PATH
        ]
        mutations["target-missing"] = target_missing

        for field, value in (
            ("kind", "symlink"),
            ("mode", 0o755),
            ("bytes", 1_211),
            ("sha256", "f" * 64),
        ):
            changed = copy.deepcopy(source)
            target = mutate_row(changed, RUN.COMPILE_RUNNER_TARGET_PATH)
            target[field] = value
            if field == "kind":
                target["target"] = "other.sh"
            mutations[f"target-{field}"] = changed

        with mock.patch.object(BASE, "validate_source_record", return_value=[]):
            self.assertEqual(RUN.validate_selected_source(source), [])
            for name, changed in mutations.items():
                with self.subTest(name=name):
                    self.assertTrue(RUN.validate_selected_source(changed))

        self.assertEqual(
            RUN._resolve_manifest_link(
                RUN.COMPILE_BENCH_RUNNER_PATH, "../compile/run_test.sh"
            ),
            RUN.COMPILE_RUNNER_TARGET_PATH,
        )
        self.assertIsNone(
            RUN._resolve_manifest_link(RUN.COMPILE_BENCH_RUNNER_PATH, "/absolute")
        )
        self.assertIsNone(
            RUN._resolve_manifest_link(RUN.COMPILE_BENCH_RUNNER_PATH, "../../../escape")
        )


if __name__ == "__main__":
    unittest.main()
