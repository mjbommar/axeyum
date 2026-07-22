"""Real-process E2 aggregate cgroup integration and kill/resume gates."""

from __future__ import annotations

import json
import os
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SMTCOMP = ROOT / "scripts" / "smtcomp_repro"
FIXTURES = SMTCOMP / "fixtures" / "e2"
sys.path.insert(0, str(SMTCOMP))

from resume_contract import ContractError, canonical_bytes, digest  # noqa: E402
from resume_fs import load_bundle, read_canonical_json, recover_shard_lease  # noqa: E402
from resume_runner import (  # noqa: E402
    cgroup_run_manifest,
    export_legacy_raw,
    selection_input_manifest,
)


def cgroup_host_available() -> tuple[bool, str]:
    if sys.platform != "linux":
        return False, "Linux cgroup v2 is required"
    if shutil.which("systemd-run") is None:
        return False, "systemd-run is unavailable"
    if not (Path("/sys/fs/cgroup") / "cgroup.controllers").is_file():
        return False, "the unified cgroup-v2 hierarchy is unavailable"
    private = Path(f"/run/user/{os.getuid()}/systemd/private")
    if not private.exists():
        return False, "the user systemd manager is unavailable"
    return True, ""


class E2Layout:
    def __init__(
        self,
        root: Path,
        *,
        kill_fixture: bool = False,
        wall_limit_ms: int = 500,
        marker: Path | None = None,
    ):
        self.root = root
        family = FIXTURES / "non-incremental" / "QF_BV" / "e2"
        if kill_fixture:
            self.benchmarks = [family / "kill-after-start.smt2"]
            self.shard_count = 1
            self.worker_slots = 1
        else:
            self.benchmarks = sorted(family.glob("case-*.smt2"))
            self.shard_count = 2
            self.worker_slots = 2
        self.file_list = root / "selected.txt"
        self.file_list.write_text(
            "".join(f"{path.resolve()}\n" for path in self.benchmarks),
            encoding="utf-8",
        )
        self.selection_manifest = root / "selection.json"
        self.selection_manifest.write_bytes(
            canonical_bytes(selection_input_manifest(self.file_list, "non-incremental/"))
        )
        self.corpus_manifest = root / "corpus.json"
        self.corpus_manifest.write_bytes(
            canonical_bytes(
                {
                    "schema": "axeyum.smtcomp-e2-test-corpus.v1",
                    "fixture_root": str(FIXTURES.resolve()),
                }
            )
        )
        self.environment_manifest = root / "environment.json"
        self.environment_manifest.write_bytes(
            canonical_bytes(
                {
                    "schema": "axeyum.smtcomp-e2-test-environment.v1",
                    "host": socket.gethostname(),
                    "cgroup": "systemd-user-service-v2",
                }
            )
        )
        self.command_template = [str((FIXTURES / "fake_solver.py").resolve()), "{bench}"]
        if marker is not None:
            self.command_template.append(str(marker))
        self.memory_limit_bytes = 64 * 1024**2
        self.aggregate_memory_bytes = self.worker_slots * self.memory_limit_bytes
        self.wall_limit_ms = wall_limit_ms
        self.run = cgroup_run_manifest(
            repository_root=ROOT,
            source_root=SMTCOMP,
            file_list=self.file_list,
            selection_manifest=self.selection_manifest,
            corpus_manifest=self.corpus_manifest,
            environment_manifest=self.environment_manifest,
            solver_id="e2-fake",
            command_template=self.command_template,
            track="single_query",
            wall_limit_ms=self.wall_limit_ms,
            memory_limit_bytes=self.memory_limit_bytes,
            cores=1,
            shard_count=self.shard_count,
            worker_slots=self.worker_slots,
            aggregate_memory_bytes=self.aggregate_memory_bytes,
            pids_max=64,
        )
        self.run_manifest = root / "run.json"
        self.run_manifest.write_bytes(canonical_bytes(self.run))
        self.run_dir = root / "evidence"
        self.raw = root / "raw.json"

    def command(self) -> list[str]:
        return [
            sys.executable,
            str(SMTCOMP / "compete.py"),
            "--host-run",
            "--file-list",
            str(self.file_list),
            "--solver",
            "e2-fake=" + " ".join(self.command_template),
            "--track",
            "single_query",
            "--wall-limit",
            str(self.wall_limit_ms / 1000),
            "--mem-gb",
            str(self.memory_limit_bytes / 1024**3),
            "--cores",
            "1",
            "--run-manifest",
            str(self.run_manifest),
            "--run-dir",
            str(self.run_dir),
            "--selection-manifest",
            str(self.selection_manifest),
            "--corpus-manifest",
            str(self.corpus_manifest),
            "--environment-manifest",
            str(self.environment_manifest),
            "--dump-raw",
            str(self.raw),
            "--quiet",
        ]


class CgroupHostTests(unittest.TestCase):
    def require_live_host(self) -> None:
        available, reason = cgroup_host_available()
        if available:
            return
        if os.environ.get("AXEYUM_REQUIRE_SMTCOMP_CGROUP") == "1":
            self.fail(reason)
        self.skipTest(reason)

    def test_overcommit_and_environment_drift_reject_before_service_or_solver(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            layout = E2Layout(root)
            marker = root / "must-not-run.marker"
            environment = dict(os.environ, AXEYUM_SMTCOMP_E2_SOLVER_MARKER=str(marker))

            overcommitted = json.loads(canonical_bytes(layout.run))
            resources = overcommitted["resource_enforcement"]
            resources["aggregate_memory_bytes"] -= 1
            unsealed = dict(resources)
            unsealed.pop("enforcement_id")
            resources["enforcement_id"] = digest(unsealed)
            identity = overcommitted["identity"]
            identity["resource_enforcement_sha256"] = digest(resources)
            overcommitted["identity_sha256"] = digest(identity)
            layout.run_manifest.write_bytes(canonical_bytes(overcommitted))
            rejected = subprocess.run(
                layout.command(),
                cwd=ROOT,
                env=environment,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=10,
                check=False,
            )
            self.assertEqual(rejected.returncode, 2, rejected.stderr)
            self.assertIn("memory budget overcommitted", rejected.stderr)
            self.assertFalse(marker.exists())
            self.assertFalse(layout.run_dir.exists())

            layout.run_manifest.write_bytes(canonical_bytes(layout.run))
            layout.environment_manifest.write_text('{"drift":true}\n', encoding="utf-8")
            rejected = subprocess.run(
                layout.command(),
                cwd=ROOT,
                env=environment,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=10,
                check=False,
            )
            self.assertEqual(rejected.returncode, 2, rejected.stderr)
            self.assertIn("environment_class_sha256", rejected.stderr)
            self.assertFalse(marker.exists())
            self.assertFalse(layout.run_dir.exists())

    def test_real_cgroup_bounds_concurrency_and_records_kernel_counters(self) -> None:
        self.require_live_host()
        with tempfile.TemporaryDirectory() as tmp:
            layout = E2Layout(Path(tmp))
            completed = subprocess.run(
                layout.command(),
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=20,
                check=False,
            )
            self.assertEqual(completed.returncode, 0, completed.stderr)
            self.assertTrue(layout.raw.is_file())
            bundle = load_bundle(layout.run_dir)
            self.assertEqual(len(bundle.records), 4)
            sessions = sorted((layout.run_dir / "resource-sessions").iterdir())
            self.assertEqual(len(sessions), 1)
            preflight = read_canonical_json(sessions[0] / "preflight.json")
            terminal = read_canonical_json(sessions[0] / "terminal.json")
            snapshot = preflight["snapshot"]
            self.assertEqual(snapshot["memory_max_bytes"], layout.aggregate_memory_bytes)
            self.assertEqual(snapshot["memory_swap_max_bytes"], 0)
            self.assertEqual(snapshot["cpu_quota_usec"], 200_000)
            self.assertEqual(snapshot["pids_max"], 64)
            self.assertGreater(terminal["memory_peak_bytes"], 0)
            self.assertGreater(terminal["cpu_stat_delta"]["usage_usec"], 0)
            self.assertGreaterEqual(terminal["pids_peak"], 5)
            session_id = preflight["session_id"]
            for attempts in bundle.attempts.values():
                self.assertEqual({attempt["resource_session_id"] for attempt in attempts}, {session_id})

            terminal["memory_peak_bytes"] += 1
            terminal_path = sessions[0] / "terminal.json"
            terminal_path.chmod(0o644)
            terminal_path.write_bytes(canonical_bytes(terminal))
            with self.assertRaisesRegex(ContractError, "resource evidence hash mismatch"):
                export_legacy_raw(layout.run_dir, layout.root / "tampered-raw.json")

            terminal["memory_peak_bytes"] -= 1
            terminal["worker_exit_codes"].pop()
            terminal.pop("record_sha256")
            terminal["record_sha256"] = digest(terminal)
            terminal_path.write_bytes(canonical_bytes(terminal))
            with self.assertRaisesRegex(ContractError, "worker status mismatch"):
                export_legacy_raw(layout.run_dir, layout.root / "resealed-raw.json")

    def test_killed_host_runner_leaves_honest_session_and_resumes(self) -> None:
        self.require_live_host()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            marker = root / "solver.marker"
            layout = E2Layout(
                root,
                kill_fixture=True,
                wall_limit_ms=1000,
                marker=marker,
            )
            process = subprocess.Popen(
                layout.command(),
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            preflight_path: Path | None = None
            try:
                deadline = time.monotonic() + 10
                while time.monotonic() < deadline:
                    matches = list((layout.run_dir / "resource-sessions").glob("*/preflight.json"))
                    if matches and marker.exists():
                        preflight_path = matches[0]
                        break
                    if process.poll() is not None:
                        _stdout, stderr = process.communicate()
                        self.fail(f"host runner exited before kill point: {stderr}")
                    time.sleep(0.02)
                self.assertIsNotNone(preflight_path, "host runner did not publish E2 preflight")
                preflight = read_canonical_json(preflight_path)
                os.kill(preflight["launcher_pid"], signal.SIGKILL)
                process.communicate(timeout=10)
                self.assertNotEqual(process.returncode, 0)
            finally:
                if process.poll() is None:
                    process.kill()
                    process.communicate(timeout=5)

            old_session = preflight_path.parent
            self.assertFalse((old_session / "terminal.json").exists())
            for lease_path in sorted((layout.run_dir / "leases").glob("*.json")):
                owner = read_canonical_json(lease_path)
                recover_shard_lease(
                    layout.run_dir, lease_path.stem, owner["owner_id"]
                )
            resumed = subprocess.run(
                layout.command(),
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=20,
                check=False,
            )
            self.assertEqual(resumed.returncode, 0, resumed.stderr)
            completion = read_canonical_json(layout.run_dir / "resource-completion.json")
            self.assertIn(preflight["session_id"], completion["unclosed_session_ids"])
            self.assertEqual(len(completion["terminal_session_ids"]), 1)
            bundle = load_bundle(layout.run_dir)
            attempts = bundle.attempts["0"]
            self.assertEqual(len(attempts), 2)
            self.assertIsNone(attempts[0]["terminal"])
            self.assertEqual(
                bundle.completions["0"]["unclosed_attempt_ids"],
                [attempts[0]["attempt_id"]],
            )


if __name__ == "__main__":
    unittest.main()
