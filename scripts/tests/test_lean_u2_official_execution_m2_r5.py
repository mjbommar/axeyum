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
from scripts import lean_u2_official_execution_m2_r4 as R4
from scripts import lean_u2_official_execution_m2_r5 as R5
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
        stderr_payload: bytes,
    ) -> None:
        self.returncode = returncode
        self.pid = 987_654_324
        stdout.write(stdout_payload)
        stderr.write(stderr_payload)

    def poll(self) -> int:
        return self.returncode

    def wait(self, timeout: float) -> int:
        return self.returncode


class LeanU2OfficialExecutionM2R5Tests(unittest.TestCase):
    def test_history_spec_and_resource_only_delta_are_exact(self) -> None:
        R5.validate_history()
        summary = R5.validate_offline_contract()
        self.assertEqual(summary["cases"], 64)
        self.assertEqual(summary["generated"], 124)
        self.assertEqual(summary["memory_limit_bytes"], 34_359_738_368)
        spec = R5.build_spec(
            implementation_revision="1" * 40,
            source_root=Path("/r5/source"),
            toolchain_root=Path("/r5/toolchain"),
            harness_build=Path("/r5/harness"),
            junit_path=Path("/r5/attempt/test-results.xml"),
        )
        self.assertEqual(R5.validate_spec(spec), [])
        self.assertEqual(spec["run_id"], R5.RUN_ID)
        self.assertEqual(spec["attempt_id"], "attempt-003")
        self.assertEqual(spec["sequence"], 3)
        self.assertTrue(spec["prior_history"]["selected_attempt_unconsumed"])
        r4 = R4.resource_envelope()
        r5 = R5.resource_envelope()
        normalized = copy.deepcopy(r4)
        normalized["lane_id"] = r5["lane_id"]
        normalized["memory_limit"] = r5["memory_limit"]
        self.assertEqual(normalized, r5)
        self.assertEqual(R5.CONTROL_SOURCE, R4.FANOUT_SOURCE)

    def _run_fake_control(
        self, root: Path, *, returncode: int, stdout: bytes, stderr: bytes
    ) -> dict[str, object]:
        revision = "2" * 40
        control_root = Path(R5.CONTROL_ROOT_PREFIX + revision[:8])
        toolchain = root / "toolchain"
        (toolchain / "bin").mkdir(parents=True)
        lean = toolchain / "bin/lean"
        lean.write_bytes(b"synthetic")

        def factory(command: list[str], **kwargs: object) -> FakeProcess:
            self.assertEqual(command[0], str(lean))
            self.assertEqual(kwargs["env"][R5.STACK_ENV], "524288")
            self.assertTrue(kwargs["start_new_session"])
            self.assertTrue(callable(kwargs["preexec_fn"]))
            return FakeProcess(
                returncode,
                kwargs["stdout"],
                kwargs["stderr"],
                stdout_payload=stdout,
                stderr_payload=stderr,
            )

        with (
            mock.patch.object(R5, "CONTROL_ROOT_PREFIX", str(root / "control-")),
            mock.patch.object(R5, "validate_revision_preflight"),
            mock.patch.object(
                BASE,
                "sha256_file",
                side_effect=lambda path: (
                    BASE.PINNED_LEAN_SHA256
                    if Path(path) == lean
                    else __import__("hashlib").sha256(Path(path).read_bytes()).hexdigest()
                ),
            ),
        ):
            control_root = Path(R5.CONTROL_ROOT_PREFIX + revision[:8])
            completion = R5.run_control(
                implementation_revision=revision,
                control_root=control_root,
                toolchain_root=toolchain,
                popen_factory=factory,
                live_members=lambda _pgid: [],
                sample_process=lambda _pid: {
                    "VmPeak": 100,
                    "VmSize": 90,
                    "VmRSS": 80,
                    "Threads": 10,
                },
            )
            validated = R5.validate_control(
                control_root,
                require_authorized=completion["authorized_selected_execution"],
            )
        return {"root": control_root, "completion": validated}

    def test_success_control_is_complete_authorizing_and_tamper_sensitive(self) -> None:
        with tempfile.TemporaryDirectory(prefix="axeyum-r5-success-test-") as temporary:
            root = Path(temporary)
            result = self._run_fake_control(
                root, returncode=0, stdout=R5.CONTROL_SUCCESS, stderr=b""
            )
            completion = result["completion"]
            control_root = result["root"]
            self.assertTrue(completion["authorized_selected_execution"])
            self.assertFalse(completion["selected_attempt_consumed"])
            self.assertTrue(all(value == 0 for value in completion["credits"].values()))
            self.assertEqual(
                {row["path"] for row in BASE.manifest_tree(control_root)},
                {*R5.CONTROL_FIXED_PATHS, "completion.json"},
            )
            stdout = control_root / "raw/stdout.bin"
            stdout.chmod(0o644)
            stdout.write_bytes(b"tamper")
            stdout.chmod(0o444)
            with self.assertRaisesRegex(R5.R5Error, "raw.*drift"):
                R5.validate_control(control_root, require_authorized=True)

    def test_failed_control_is_completion_grade_zero_credit_and_not_authorized(self) -> None:
        with tempfile.TemporaryDirectory(prefix="axeyum-r5-failure-test-") as temporary:
            result = self._run_fake_control(
                Path(temporary),
                returncode=1,
                stdout=b"",
                stderr=b"failed to create thread\n",
            )
            completion = result["completion"]
            control_root = result["root"]
            self.assertFalse(completion["authorized_selected_execution"])
            self.assertFalse(completion["selected_attempt_consumed"])
            terminal = BASE.load_canonical(control_root / "terminal.json")
            self.assertEqual(terminal["class"], "exited")
            self.assertEqual(terminal["exit_code"], 1)
            self.assertEqual(terminal["samples"][0]["Threads"], 10)
            with self.assertRaisesRegex(R5.R5Error, "does not authorize"):
                R5.validate_control(control_root, require_authorized=True)

    def test_r5_binding_installs_32g_and_restores_m2(self) -> None:
        original = M2.MEMORY_LIMIT_BYTES
        with tempfile.TemporaryDirectory(prefix="axeyum-r5-process-test-") as temporary:
            root = Path(temporary)
            spec = R5.build_spec(
                implementation_revision="3" * 40,
                source_root=root / "source",
                toolchain_root=root / "toolchain",
                harness_build=root / "harness",
                junit_path=root / "attempt/test-results.xml",
            )
            prelaunch = BASE.seal(
                {"schema": "r5-test-prelaunch-v1", "record_sha256": ""},
                "r5-test-prelaunch-v1",
            )

            def factory(command: list[str], **kwargs: object) -> FakeProcess:
                return FakeProcess(
                    0,
                    kwargs["stdout"],
                    kwargs["stderr"],
                    stdout_payload=b"synthetic\n",
                    stderr_payload=b"",
                )

            with R5.r5_bindings():
                terminal, stdout, stderr = OLD_RUN.execute_process(
                    spec,
                    root / "attempt-process",
                    prelaunch["record_sha256"],
                    popen_factory=factory,
                    live_members=lambda _pgid: [],
                    sample_rss=lambda _pid: 4096,
                )
                self.assertEqual(
                    terminal["process"]["rlimit_as_bytes"], R5.MEMORY_LIMIT_BYTES
                )
                self.assertEqual(terminal["run_id"], R5.RUN_ID)
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
            self.assertEqual(M2.MEMORY_LIMIT_BYTES, original)

    def test_cli_offline_has_no_implicit_control_or_selected_execution(self) -> None:
        result = subprocess.run(
            [sys.executable, str(Path(R5.__file__).resolve()), "offline-check"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertIn(b"controls=0|selected_processes=0", result.stdout)
        help_result = subprocess.run(
            [sys.executable, str(Path(R5.__file__).resolve()), "--help"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(help_result.returncode, 0)
        self.assertIn(b"run-control", help_result.stdout)
        self.assertIn(b"run-r5", help_result.stdout)


if __name__ == "__main__":
    unittest.main()
