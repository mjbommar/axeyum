from __future__ import annotations

import copy
import shutil
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
from scripts import lean_u2_official_execution_m2_run as OLD_RUN


ROOT = Path(__file__).resolve().parents[2]


class FakeProcess:
    def __init__(self, returncode: int, stdout: object, stderr: object) -> None:
        self.returncode = returncode
        self.pid = 987_654_322
        stdout.write(b"synthetic R3 CTest stdout\n")
        stderr.write(b"")

    def poll(self) -> int:
        return self.returncode

    def wait(self, timeout: float) -> int:
        return self.returncode


class LeanU2OfficialExecutionM2R3Tests(unittest.TestCase):
    def test_history_spec_wrapper_and_offline_contract_are_exact(self) -> None:
        history = R3.validate_history()
        self.assertEqual(history["post"]["record_sha256"], R3.R2_POST_RECORD)
        self.assertEqual(
            history["completion"]["record_sha256"], R3.R2_COMPLETION_RECORD
        )
        summary = R3.validate_offline_contract()
        self.assertEqual(summary["cases"], 64)
        self.assertEqual(summary["generated"], 124)
        spec = R3.build_spec(
            implementation_revision="1" * 40,
            source_root=Path("/r3/source"),
            toolchain_root=Path("/r3/toolchain"),
            harness_build=Path("/r3/harness"),
            junit_path=Path("/r3/attempt/test-results.xml"),
        )
        self.assertEqual(R3.validate_spec(spec), [])
        self.assertEqual(spec["run_id"], R3.RUN_ID)
        self.assertEqual(spec["attempt_id"], "attempt-002")
        self.assertEqual(spec["sequence"], 2)
        self.assertEqual(spec["environment"][R3.STACK_ENV], "524288")
        self.assertEqual(
            spec["resource_envelope"]["task_stack_limit"],
            BASE.metric("requested", 536_870_912, "bytes"),
        )
        self.assertTrue(all(value == 0 for value in M2.ZERO_TERMINAL_CREDITS.values()))

    def test_stack_wrapper_rejects_missing_duplicate_and_invalid_values(self) -> None:
        wrapper = R3.render_environment_wrapper(
            Path("/r3/source"), Path("/r3/toolchain")
        )
        R3.validate_environment_wrapper(wrapper)
        line = b"export LEAN_STACK_SIZE_KB=524288\n"
        mutations = {
            "missing": wrapper.replace(line, b""),
            "duplicate": wrapper.replace(line, line + line),
            "zero": wrapper.replace(b"524288", b"0"),
            "non-numeric": wrapper.replace(b"524288", b"half-gig"),
            "changed": wrapper.replace(b"524288", b"262144"),
        }
        for name, changed in mutations.items():
            with self.subTest(name=name), self.assertRaises(R3.R3Error):
                R3.validate_environment_wrapper(changed)

    def test_direct_runtime_probe_is_harmless_and_environment_bound(self) -> None:
        with tempfile.TemporaryDirectory(prefix="axeyum-r3-probe-test-") as temporary:
            toolchain = Path(temporary) / "toolchain"
            (toolchain / "bin").mkdir(parents=True)
            lean = toolchain / "bin/lean"
            lean.write_bytes(b"synthetic")

            def fake_run(command: list[str], **kwargs: object) -> subprocess.CompletedProcess[bytes]:
                self.assertEqual(command[0], str(lean))
                self.assertEqual(command[1], "--run")
                self.assertEqual(kwargs["env"][R3.STACK_ENV], "524288")
                self.assertNotIn("compile", Path(command[2]).name)
                return subprocess.CompletedProcess(command, 0, b"524288\n", b"")

            result = R3.probe_stack_environment(toolchain, run_command=fake_run)
        self.assertFalse(result["selected_case"])
        self.assertEqual(result["exit_code"], 0)

    def test_family_specific_tiered_post_and_mixed_projection(self) -> None:
        diagnostic = BASE.load_canonical(R2.EVIDENCE_ROOT / "diagnostic/post.json")
        generated = copy.deepcopy(diagnostic["generated_files"])
        wrapper = R3.render_environment_wrapper(Path("/r3/source"), Path("/r3/toolchain"))
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
        post = R3.build_post_record(
            original_files=source["files"], generated_files=generated, junit=junit
        )
        self.assertEqual(len(post["generated_files"]), 124)
        self.assertEqual(len(post["retained_generated"]), 67)
        self.assertEqual(len(post["manifest_only_generated"]), 56)
        self.assertEqual(
            R3.case_generated_paths(
                next(
                    case
                    for case in M2.selected_contract()["cases"]
                    if case["id"] == "docparse/arg_0006.txt"
                )
            ),
            ["tests/docparse/arg_0006.txt.out.produced"],
        )
        projection = R3.result_projection(junit, post)
        self.assertEqual(projection["credits"]["official_passes"], 30)
        self.assertEqual(projection["credits"]["official_failures"], 34)
        self.assertEqual(projection["credits"]["paired_cells"], 0)
        self.assertEqual(projection["credits"]["parity_credit"], 0)
        changed = copy.deepcopy(post)
        changed["assurance"]["metadata_only_count"] = 55
        changed = BASE.seal(changed, M2.POST_SCHEMA)
        with self.assertRaisesRegex(R3.R3Error, "post-run projection"):
            R3.result_projection(junit, changed)

    def test_r3_binding_process_adapter_and_completion_no_overwrite(self) -> None:
        original_run_id = M2.RUN_ID
        with tempfile.TemporaryDirectory(prefix="axeyum-r3-process-test-") as temporary:
            root = Path(temporary)
            spec = R3.build_spec(
                implementation_revision="2" * 40,
                source_root=root / "source",
                toolchain_root=root / "toolchain",
                harness_build=root / "harness",
                junit_path=root / "attempt/test-results.xml",
            )
            prelaunch = BASE.seal(
                {"schema": "r3-test-prelaunch-v1", "record_sha256": ""},
                "r3-test-prelaunch-v1",
            )

            def factory(command: list[str], **kwargs: object) -> FakeProcess:
                self.assertEqual(kwargs["env"][R3.STACK_ENV], "524288")
                return FakeProcess(0, kwargs["stdout"], kwargs["stderr"])

            with R3.r3_bindings():
                terminal, stdout, stderr = OLD_RUN.execute_process(
                    spec,
                    root / "attempt-process",
                    prelaunch["record_sha256"],
                    popen_factory=factory,
                    live_members=lambda _pgid: [],
                    sample_rss=lambda _pid: 4096,
                )
                self.assertEqual(terminal["run_id"], R3.RUN_ID)
                self.assertEqual(terminal["attempt_id"], R3.ATTEMPT_ID)
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
            self.assertEqual(M2.RUN_ID, original_run_id)

            completion = BASE.seal(
                {"schema": R3.COMPLETION_SCHEMA, "record_sha256": ""},
                R3.COMPLETION_SCHEMA,
            )
            evidence = root / "evidence"
            evidence.mkdir()
            changed_completion = BASE.seal(
                {
                    "schema": R3.COMPLETION_SCHEMA,
                    "state": "conflict",
                    "record_sha256": "",
                },
                R3.COMPLETION_SCHEMA,
            )
            with mock.patch.object(
                R3,
                "build_completion",
                side_effect=[completion, changed_completion],
            ):
                self.assertEqual(R3.install_completion(evidence), completion)
                with self.assertRaises(BASE.STORE.CheckpointConflict):
                    R3.install_completion(evidence)

    def test_cli_smoke_has_no_implicit_selected_execution(self) -> None:
        checked = subprocess.run(
            [sys.executable, str(Path(R3.__file__).resolve()), "offline-check"],
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
            [sys.executable, str(Path(R3.__file__).resolve()), "--help"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(help_result.returncode, 0, help_result.stderr.decode())
        self.assertIn(b"run-r3", help_result.stdout)

    def test_retained_timeout_is_incomplete_tamper_sensitive_and_zero_credit(self) -> None:
        result = R3.validate_incomplete_evidence(R3.DEFAULT_EVIDENCE_ROOT)
        self.assertEqual(result["terminal"]["class"], "wall-timeout")
        self.assertEqual(result["files"], 17)
        self.assertEqual(result["bytes"], 4_908_035)
        self.assertEqual(result["official_outcomes"], 0)
        self.assertEqual(result["parity_credit"], 0)
        with tempfile.TemporaryDirectory(prefix="axeyum-r3-incomplete-test-") as temporary:
            root = Path(temporary) / "evidence"
            shutil.copytree(R3.DEFAULT_EVIDENCE_ROOT, root)
            for path in root.rglob("*"):
                if path.is_file():
                    path.chmod(0o444)
            stdout = root / "raw/stdout.bin"
            stdout.chmod(0o644)
            stdout.write_bytes(stdout.read_bytes() + b"tamper")
            stdout.chmod(0o444)
            with self.assertRaisesRegex(R3.R3Error, "terminal.*drift"):
                R3.validate_incomplete_evidence(root)

        authority = BASE.load_json(
            ROOT
            / "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r3-"
            "attempt-002-result-v1.json"
        )
        self.assertTrue(BASE.valid_seal(authority, authority["schema"]))
        self.assertEqual(authority["status"], "invalid-wall-timeout")
        self.assertEqual(authority["retained_evidence"]["files"], result["files"])
        self.assertEqual(authority["retained_evidence"]["bytes"], result["bytes"])
        self.assertEqual(
            authority["retained_evidence"]["manifest_sha256"],
            result["manifest_sha256"],
        )
        self.assertEqual(
            authority["terminal"]["record_sha256"],
            result["terminal"]["record_sha256"],
        )
        self.assertTrue(all(value == 0 for value in authority["credits"].values()))


if __name__ == "__main__":
    unittest.main()
