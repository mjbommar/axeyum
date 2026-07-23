from __future__ import annotations

import copy
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import lean_u2_official_execution as BASE
from scripts import lean_u2_official_execution_m2 as M2
from scripts import lean_u2_official_execution_m2_r2 as R2
from scripts import lean_u2_official_execution_m2_r3 as R3
from scripts import lean_u2_official_execution_m2_r4 as R4
from scripts import lean_u2_official_execution_m2_run as OLD_RUN


ROOT = Path(__file__).resolve().parents[2]


class FakeProcess:
    def __init__(
        self,
        returncode: int,
        stdout: object,
        stderr: object,
        *,
        stdout_payload: bytes,
        stderr_payload: bytes = b"",
    ) -> None:
        self.returncode = returncode
        self.pid = 987_654_323
        stdout.write(stdout_payload)
        stderr.write(stderr_payload)

    def poll(self) -> int:
        return self.returncode

    def wait(self, timeout: float) -> int:
        return self.returncode


class LeanU2OfficialExecutionM2R4Tests(unittest.TestCase):
    def test_history_spec_roots_and_only_resource_delta_are_exact(self) -> None:
        history = R4.validate_history()
        self.assertEqual(
            history["authority"]["record_sha256"], R4.R3_AUTHORITY_RECORD
        )
        self.assertEqual(
            history["incomplete"]["terminal"]["record_sha256"],
            R4.R3_TERMINAL_RECORD,
        )
        summary = R4.validate_offline_contract()
        self.assertEqual(summary["cases"], 64)
        self.assertEqual(summary["generated"], 124)
        self.assertEqual(summary["memory_limit_bytes"], 17_179_869_184)
        self.assertNotEqual(R4.DEFAULT_EVIDENCE_ROOT, R3.DEFAULT_EVIDENCE_ROOT)
        self.assertNotEqual(R4.WORK_ROOT_PREFIX, R3.WORK_ROOT_PREFIX)

        spec = R4.build_spec(
            implementation_revision="1" * 40,
            source_root=Path("/r4/source"),
            toolchain_root=Path("/r4/toolchain"),
            harness_build=Path("/r4/harness"),
            junit_path=Path("/r4/attempt/test-results.xml"),
        )
        self.assertEqual(R4.validate_spec(spec), [])
        self.assertEqual(spec["run_id"], R4.RUN_ID)
        self.assertEqual(spec["attempt_id"], "attempt-003")
        self.assertEqual(spec["sequence"], 3)
        self.assertEqual(
            spec["prior_history"]["r3_authority_record_sha256"],
            R4.R3_AUTHORITY_RECORD,
        )

        r3_envelope = R3.resource_envelope()
        r4_envelope = R4.resource_envelope()
        self.assertEqual(r3_envelope["memory_limit"]["value"], 8_589_934_592)
        self.assertEqual(r4_envelope["memory_limit"]["value"], 17_179_869_184)
        normalized_r3 = copy.deepcopy(r3_envelope)
        normalized_r4 = copy.deepcopy(r4_envelope)
        normalized_r3["lane_id"] = normalized_r4["lane_id"]
        normalized_r3["memory_limit"] = normalized_r4["memory_limit"]
        self.assertEqual(normalized_r3, normalized_r4)
        self.assertEqual(
            R4.render_environment_wrapper(Path("/same/source"), Path("/same/toolchain")),
            R3.render_environment_wrapper(Path("/same/source"), Path("/same/toolchain")),
        )

    def test_fanout_control_is_harmless_bound_and_cleanup_sensitive(self) -> None:
        self.assertIn(b"fun task => do IO.ofExcept", R4.FANOUT_SOURCE)
        with tempfile.TemporaryDirectory(prefix="axeyum-r4-fanout-test-") as temporary:
            toolchain = Path(temporary) / "toolchain"
            (toolchain / "bin").mkdir(parents=True)
            lean = toolchain / "bin/lean"
            lean.write_bytes(b"synthetic")
            limit_calls: list[int] = []

            def fake_limit(limit: int) -> object:
                limit_calls.append(limit)
                return lambda: None

            def factory(command: list[str], **kwargs: object) -> FakeProcess:
                self.assertEqual(command[0], str(lean))
                self.assertEqual(command[1], "--run")
                self.assertEqual(kwargs["env"][R4.STACK_ENV], "524288")
                self.assertTrue(kwargs["start_new_session"])
                self.assertTrue(callable(kwargs["preexec_fn"]))
                return FakeProcess(
                    0,
                    kwargs["stdout"],
                    kwargs["stderr"],
                    stdout_payload=R4.FANOUT_SUCCESS,
                )

            with mock.patch.object(BASE.PROCESS, "_limit_hook", side_effect=fake_limit):
                result = R4.probe_fanout(
                    toolchain,
                    popen_factory=factory,
                    live_members=lambda _pgid: [],
                    sample_rss=lambda _pid: 8192,
                )
            self.assertEqual(limit_calls, [R4.MEMORY_LIMIT_BYTES])
            self.assertTrue(BASE.valid_seal(result, R4.FANOUT_SCHEMA))
            self.assertFalse(result["selected_case"])
            self.assertEqual(result["assigned_case_ids"], [])
            self.assertEqual(result["source"]["bytes"], len(R4.FANOUT_SOURCE))
            self.assertEqual(result["terminal"]["peak_direct_rss"]["value"], 8192)
            self.assertEqual(result["cleanup"]["live_non_zombie_pids_after_cleanup"], [])
            self.assertTrue(all(value == 0 for value in result["credits"].values()))

            def bad_factory(command: list[str], **kwargs: object) -> FakeProcess:
                return FakeProcess(
                    0,
                    kwargs["stdout"],
                    kwargs["stderr"],
                    stdout_payload=b"wrong\n",
                )

            with self.assertRaisesRegex(R4.R4Error, "fanout control failed"):
                R4.probe_fanout(
                    toolchain,
                    popen_factory=bad_factory,
                    live_members=lambda _pgid: [],
                )

    def test_r4_binding_installs_16g_process_adapter_and_restores_globals(self) -> None:
        original_memory = M2.MEMORY_LIMIT_BYTES
        with tempfile.TemporaryDirectory(prefix="axeyum-r4-process-test-") as temporary:
            root = Path(temporary)
            spec = R4.build_spec(
                implementation_revision="2" * 40,
                source_root=root / "source",
                toolchain_root=root / "toolchain",
                harness_build=root / "harness",
                junit_path=root / "attempt/test-results.xml",
            )
            prelaunch = BASE.seal(
                {"schema": "r4-test-prelaunch-v1", "record_sha256": ""},
                "r4-test-prelaunch-v1",
            )

            def factory(command: list[str], **kwargs: object) -> FakeProcess:
                self.assertEqual(kwargs["env"][R4.STACK_ENV], "524288")
                return FakeProcess(
                    0,
                    kwargs["stdout"],
                    kwargs["stderr"],
                    stdout_payload=b"synthetic R4 CTest stdout\n",
                )

            with R4.r4_bindings():
                terminal, stdout, stderr = OLD_RUN.execute_process(
                    spec,
                    root / "attempt-process",
                    prelaunch["record_sha256"],
                    popen_factory=factory,
                    live_members=lambda _pgid: [],
                    sample_rss=lambda _pid: 4096,
                )
                self.assertEqual(
                    terminal["process"]["rlimit_as_bytes"], R4.MEMORY_LIMIT_BYTES
                )
                self.assertEqual(terminal["run_id"], R4.RUN_ID)
                self.assertEqual(
                    OLD_RUN.validate_terminal_record(
                        terminal,
                        prelaunch=prelaunch,
                        stdout=stdout,
                        stderr=stderr,
                        require_eligible=True,
                    ),
                    [],
                )
            self.assertEqual(M2.MEMORY_LIMIT_BYTES, original_memory)

    def test_family_store_projection_remains_124_67_56_1_and_zero_terminal(self) -> None:
        diagnostic = BASE.load_canonical(R2.EVIDENCE_ROOT / "diagnostic/post.json")
        generated = copy.deepcopy(diagnostic["generated_files"])
        wrapper = R4.render_environment_wrapper(Path("/r4/source"), Path("/r4/toolchain"))
        wrapper_row = next(
            row for row in generated if row["path"] == "tests/with_stage1_test_env.sh"
        )
        wrapper_row.update(
            {
                "kind": "file",
                "mode": 0o755,
                "bytes": len(wrapper),
                "sha256": BASE.sha256_bytes(wrapper),
                "target": None,
            }
        )
        junit = BASE.load_canonical(R2.EVIDENCE_ROOT / "junit.json")
        source = BASE.load_canonical(R2.EVIDENCE_ROOT / "source.json")
        with R4.r4_bindings():
            post = R4.build_post_record(
                original_files=source["files"], generated_files=generated, junit=junit
            )
            projection = R4.result_projection(junit, post)
        self.assertEqual(len(post["generated_files"]), 124)
        self.assertEqual(len(post["retained_generated"]), 67)
        self.assertEqual(len(post["manifest_only_generated"]), 56)
        self.assertEqual(len(post["existing_wrapper"]), 1)
        self.assertEqual(projection["run_id"], R4.RUN_ID)
        self.assertEqual(projection["attempt_id"], R4.ATTEMPT_ID)
        self.assertEqual(projection["credits"]["official_passes"], 30)
        self.assertEqual(projection["credits"]["official_failures"], 34)
        for key, value in M2.ZERO_TERMINAL_CREDITS.items():
            self.assertEqual(projection["credits"][key], value)

    def test_cli_smoke_has_no_implicit_control_or_selected_execution(self) -> None:
        checked = subprocess.run(
            [sys.executable, str(Path(R4.__file__).resolve()), "offline-check"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(checked.returncode, 0, checked.stderr.decode())
        self.assertIn(
            b"selected_processes=0|outcomes=0|pairs=0|parity=0", checked.stdout
        )
        help_result = subprocess.run(
            [sys.executable, str(Path(R4.__file__).resolve()), "--help"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(help_result.returncode, 0, help_result.stderr.decode())
        self.assertIn(b"probe-fanout", help_result.stdout)
        self.assertIn(b"run-r4", help_result.stdout)


if __name__ == "__main__":
    unittest.main()
