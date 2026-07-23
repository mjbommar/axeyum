"""E1b active-runner, lifecycle, lease, sidecar, and export gates."""

from __future__ import annotations

import hashlib
import json
import multiprocessing
import os
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
sys.path.insert(0, str(SMTCOMP))

from resume_contract import ContractError, canonical_bytes, digest  # noqa: E402
from resume_fs import (  # noqa: E402
    LeaseConflict,
    acquire_shard_lease,
    load_bundle,
    read_canonical_json,
    recover_shard_lease,
    validate_bundle_directory,
)
from resume_runner import (  # noqa: E402
    cgroup_run_manifest,
    execute_resumable,
    export_legacy_raw,
    fixture_run_manifest,
    official_selection_input_manifest,
    selection_input_manifest,
)
from runner import RunResult  # noqa: E402
from scoring import Status  # noqa: E402


FAKE_SOLVER = """#!/usr/bin/env python3
import os
import pathlib
import sys
import time

benchmark = pathlib.Path(sys.argv[1])
if len(sys.argv) > 2:
    pathlib.Path(sys.argv[2]).write_text(str(os.getpid()), encoding="ascii")
text = benchmark.read_text(encoding="utf-8")
if "EXPECT_UNSAT" in text:
    print("unsat", flush=True)
else:
    print("sat", flush=True)
if "HANG_AFTER_VERDICT" in text:
    time.sleep(60)
"""


class Layout:
    def __init__(self, root: Path, *, hang: bool = False, marker: Path | None = None):
        self.root = root
        family = root / "corpus" / "non-incremental" / "QF_BV" / "fixture"
        family.mkdir(parents=True)
        first = family / "case-a.smt2"
        second = family / "case-b.smt2"
        first.write_text(
            "(set-logic QF_BV)\n(set-info :status sat)\n(check-sat)\n"
            + ("; HANG_AFTER_VERDICT\n" if hang else ""),
            encoding="utf-8",
        )
        second.write_text(
            "(set-logic QF_BV)\n(set-info :status unsat)\n(check-sat)\n"
            "; EXPECT_UNSAT\n",
            encoding="utf-8",
        )
        self.benchmarks = [first, second]
        self.file_list = root / "selected.txt"
        self.file_list.write_text(
            "".join(f"{path}\n" for path in self.benchmarks), encoding="utf-8"
        )
        self.selection_manifest = root / "selection-source.json"
        self.selection_manifest.write_bytes(
            canonical_bytes(selection_input_manifest(self.file_list, "non-incremental/"))
        )
        self.corpus_manifest = root / "corpus-source.json"
        self.corpus_manifest.write_bytes(b'{"fixture":"corpus"}\n')
        self.environment_manifest = root / "environment-source.json"
        self.environment_manifest.write_bytes(b'{"fixture":"environment"}\n')
        self.solver = root / "fake-solver"
        self.solver.write_text(FAKE_SOLVER, encoding="utf-8")
        self.solver.chmod(0o755)
        self.command_template = [str(self.solver), "{bench}"]
        if marker is not None:
            self.command_template.append(str(marker))
        self.memory_limit_bytes = 512 * 1024**2
        self.wall_limit_ms = 50
        run = fixture_run_manifest(
            repository_root=ROOT,
            source_root=SMTCOMP,
            file_list=self.file_list,
            selection_manifest=self.selection_manifest,
            corpus_manifest=self.corpus_manifest,
            environment_manifest=self.environment_manifest,
            solver_id="fake",
            command_template=self.command_template,
            track="single_query",
            wall_limit_ms=self.wall_limit_ms,
            memory_limit_bytes=self.memory_limit_bytes,
            cores=1,
            shard_count=1,
        )
        self.run_manifest = root / "run-manifest.json"
        self.run_manifest.write_bytes(canonical_bytes(run))

    def execute(
        self,
        run_dir: Path,
        *,
        runner=None,
        phase_hook=None,
        official_selection_root: Path | None = None,
    ) -> bool:
        kwargs = {}
        if runner is not None:
            kwargs["runner"] = runner
        if phase_hook is not None:
            kwargs["phase_hook"] = phase_hook
        if official_selection_root is not None:
            kwargs["official_selection_root"] = official_selection_root
        return execute_resumable(
            run_manifest=self.run_manifest,
            run_dir=run_dir,
            repository_root=ROOT,
            source_root=SMTCOMP,
            file_list=self.file_list,
            selection_manifest=self.selection_manifest,
            corpus_manifest=self.corpus_manifest,
            environment_manifest=self.environment_manifest,
            solver_id="fake",
            command_template=self.command_template,
            track="single_query",
            wall_limit_ms=self.wall_limit_ms,
            memory_limit_bytes=self.memory_limit_bytes,
            cores=1,
            shard_index=0,
            shard_count=1,
            benchmark_id_marker="non-incremental/",
            verbose=False,
            **kwargs,
        )

    def cli(self, run_dir: Path, *, raw: Path | None = None) -> list[str]:
        solver = "fake=" + " ".join(self.command_template)
        command = [
            sys.executable,
            str(SMTCOMP / "compete.py"),
            "--file-list",
            str(self.file_list),
            "--solver",
            solver,
            "--track",
            "single_query",
            "--wall-limit",
            str(self.wall_limit_ms / 1000),
            "--mem-gb",
            "0.5",
            "--cores",
            "1",
            "--shard",
            "0/1",
            "--run-manifest",
            str(self.run_manifest),
            "--run-dir",
            str(run_dir),
            "--selection-manifest",
            str(self.selection_manifest),
            "--corpus-manifest",
            str(self.corpus_manifest),
            "--environment-manifest",
            str(self.environment_manifest),
            "--quiet",
        ]
        if raw is not None:
            command.extend(["--dump-raw", str(raw)])
        return command


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def reseal_selection_root(root: Path, completion: dict) -> Path:
    payload = {
        key: value for key, value in completion.items() if key != "payload_sha256"
    }
    completion["payload_sha256"] = digest(payload)
    complete = root / "complete.json"
    complete.write_bytes(canonical_bytes(completion))
    accepted = root.parent / f"accepted-{file_sha256(complete)}"
    root.rename(accepted)
    return accepted


def install_official_selection(
    layout: Layout, *, execution_benchmarks: list[Path] | None = None
) -> Path:
    attempt = layout.root / "selection-attempt"
    attempt.mkdir()
    benchmark_ids = [
        str(path).split("non-incremental/", 1)[1] for path in layout.benchmarks
    ]
    benchmark_ids = [f"non-incremental/{benchmark_id}" for benchmark_id in benchmark_ids]
    selected = attempt / "official-selected.txt"
    selected.write_text("".join(f"{value}\n" for value in benchmark_ids), encoding="utf-8")
    ledger = attempt / "selected-files.jsonl"
    ledger.write_bytes(
        b"".join(
            canonical_bytes(
                {
                    "archive": "QF_BV.tar.zst",
                    "benchmark_id": benchmark_id,
                    "bytes": path.stat().st_size,
                    "logic": "QF_BV",
                    "sha256": file_sha256(path),
                }
            )
            for benchmark_id, path in zip(benchmark_ids, layout.benchmarks)
        )
    )
    completion = {
        "artifacts": {
            "official-selected.txt": file_sha256(selected),
            "selected-files.jsonl": file_sha256(ledger),
        },
        "authority_sha256": "a" * 64,
        "metadata_rows": len(benchmark_ids),
        "payload_sha256": "",
        "schema": "axeyum-smtcomp-official-selection-v1",
        "selected_files": len(benchmark_ids),
        "selection_observed": True,
        "status": "complete",
    }
    accepted = reseal_selection_root(attempt, completion)
    if execution_benchmarks is not None:
        layout.file_list.write_text(
            "".join(f"{path}\n" for path in execution_benchmarks),
            encoding="utf-8",
        )
    layout.selection_manifest.write_bytes(
        canonical_bytes(
            official_selection_input_manifest(
                layout.file_list, "non-incremental/", accepted
            )
        )
    )
    run = fixture_run_manifest(
        repository_root=ROOT,
        source_root=SMTCOMP,
        file_list=layout.file_list,
        selection_manifest=layout.selection_manifest,
        corpus_manifest=layout.corpus_manifest,
        environment_manifest=layout.environment_manifest,
        solver_id="fake",
        command_template=layout.command_template,
        track="single_query",
        wall_limit_ms=layout.wall_limit_ms,
        memory_limit_bytes=layout.memory_limit_bytes,
        cores=1,
        shard_count=1,
    )
    layout.run_manifest.write_bytes(canonical_bytes(run))
    return accepted


def fixed_result(command: list[str], **_kwargs) -> RunResult:
    unsat = command[1].endswith("case-b.smt2")
    status = Status.UNSAT if unsat else Status.SAT
    output = (status.value + "\n").encode("ascii")
    duration = 0.002 if unsat else 0.001
    return RunResult(
        reported=status,
        observed=status,
        wall_time=duration,
        scoring_wall_time=duration,
        runner_elapsed=duration,
        cpu_time=duration / 2,
        exit_code=0,
        signal=None,
        termination_class="completed",
        resource_limit_kind=None,
        timed_out=False,
        mem_exceeded=False,
        peak_rss_bytes=1024,
        stdout=output.decode("ascii"),
        stderr="",
        stdout_bytes=output,
        stderr_bytes=b"",
    )


class ResumeRunnerTests(unittest.TestCase):
    def test_admitted_selection_executes_ordered_subset(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            layout = Layout(root)
            accepted = install_official_selection(
                layout, execution_benchmarks=[layout.benchmarks[1]]
            )
            run_dir = root / "admitted-subset-run"
            self.assertTrue(
                layout.execute(
                    run_dir,
                    runner=fixed_result,
                    official_selection_root=accepted,
                )
            )
            selection = read_canonical_json(layout.selection_manifest)
            self.assertEqual(selection["official_selection"]["selected_files"]["rows"], 2)
            self.assertEqual(len(selection["benchmarks"]), 1)
            self.assertEqual(selection["benchmarks"][0]["sequence"], 0)
            self.assertEqual(selection["benchmarks"][0]["benchmark_id"], "QF_BV/fixture/case-b.smt2")

    def test_admitted_subset_rejects_nonmember_order_duplicate_and_unrequested_drift(
        self,
    ) -> None:
        for mutation in range(1, 6):
            with (
                self.subTest(mutation=f"S5.1-M{mutation:02d}"),
                tempfile.TemporaryDirectory() as tmp,
            ):
                root = Path(tmp)
                layout = Layout(root)
                accepted = install_official_selection(
                    layout, execution_benchmarks=[layout.benchmarks[0]]
                )
                run_dir = root / "must-not-exist"
                if mutation == 1:
                    missing = layout.benchmarks[0].with_name("not-selected.smt2")
                    missing.write_text(layout.benchmarks[0].read_text(encoding="utf-8"))
                    layout.file_list.write_text(f"{missing}\n", encoding="utf-8")
                    with self.assertRaisesRegex(ContractError, "not officially selected"):
                        official_selection_input_manifest(
                            layout.file_list, "non-incremental/", accepted
                        )
                elif mutation in {2, 3}:
                    execution = (
                        [layout.benchmarks[1], layout.benchmarks[0]]
                        if mutation == 2
                        else [layout.benchmarks[0], layout.benchmarks[0]]
                    )
                    layout.file_list.write_text(
                        "".join(f"{path}\n" for path in execution),
                        encoding="utf-8",
                    )
                    with self.assertRaisesRegex(ContractError, "strictly ordered"):
                        official_selection_input_manifest(
                            layout.file_list, "non-incremental/", accepted
                        )
                elif mutation == 4:
                    ledger_path = accepted / "selected-files.jsonl"
                    rows = ledger_path.read_bytes().splitlines(keepends=True)
                    second = json.loads(rows[1])
                    second["benchmark_id"] = second["benchmark_id"].replace(
                        "case-b", "case-z"
                    )
                    rows[1] = canonical_bytes(second)
                    ledger_path.write_bytes(b"".join(rows))
                    completion = read_canonical_json(accepted / "complete.json")
                    completion["artifacts"]["selected-files.jsonl"] = file_sha256(
                        ledger_path
                    )
                    staging = accepted.with_name("selection-mutated")
                    accepted.rename(staging)
                    accepted = reseal_selection_root(staging, completion)
                    with self.assertRaisesRegex(ContractError, "ledger identity mismatch"):
                        layout.execute(
                            run_dir,
                            runner=fixed_result,
                            official_selection_root=accepted,
                        )
                else:
                    with layout.benchmarks[0].open("ab") as benchmark:
                        benchmark.write(b"; subset physical drift\n")
                    with self.assertRaisesRegex(ContractError, "benchmark bytes differ"):
                        layout.execute(
                            run_dir,
                            runner=fixed_result,
                            official_selection_root=accepted,
                        )
                self.assertFalse(run_dir.exists())

    def test_admitted_selection_executes_tiny_fixture(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            layout = Layout(root)
            accepted = install_official_selection(layout)
            run_dir = root / "admitted-run"
            self.assertTrue(
                layout.execute(
                    run_dir,
                    runner=fixed_result,
                    official_selection_root=accepted,
                )
            )
            selection = read_canonical_json(layout.selection_manifest)
            self.assertEqual(selection["schema"], "axeyum.smtcomp-selection-input.v2")
            self.assertEqual(
                selection["official_selection"]["completion_sha256"],
                accepted.name.removeprefix("accepted-"),
            )
            self.assertEqual(len(selection["benchmarks"]), 2)

    def test_admitted_selection_mutations_reject_before_run_directory(self) -> None:
        for mutation in range(1, 9):
            with (
                self.subTest(mutation=f"S5-M{mutation:02d}"),
                tempfile.TemporaryDirectory() as tmp,
            ):
                root = Path(tmp)
                layout = Layout(root)
                accepted = install_official_selection(layout)
                if mutation == 1:
                    completion = read_canonical_json(accepted / "complete.json")
                    completion["status"] = "incomplete"
                    staging = accepted.with_name("selection-mutated")
                    accepted.rename(staging)
                    accepted = reseal_selection_root(staging, completion)
                elif mutation == 2:
                    completion = read_canonical_json(accepted / "complete.json")
                    completion["payload_sha256"] = "0" * 64
                    complete = accepted / "complete.json"
                    complete.write_bytes(canonical_bytes(completion))
                    staging = accepted.with_name("selection-mutated")
                    accepted.rename(staging)
                    completion_sha256 = file_sha256(staging / "complete.json")
                    destination = staging.parent / f"accepted-{completion_sha256}"
                    staging.rename(destination)
                    accepted = destination
                elif mutation == 3:
                    destination = accepted.with_name(f"accepted-{'0' * 64}")
                    accepted.rename(destination)
                    accepted = destination
                elif mutation == 4:
                    with (accepted / "official-selected.txt").open("ab") as selected:
                        selected.write(b"non-incremental/QF_BV/z/extra.smt2\n")
                elif mutation == 5:
                    with (accepted / "selected-files.jsonl").open("ab") as ledger:
                        ledger.write(b"{}\n")
                elif mutation == 6:
                    selected_path = accepted / "official-selected.txt"
                    selected = selected_path.read_text(encoding="utf-8").splitlines()
                    selected_path.write_text(
                        "".join(f"{value}\n" for value in reversed(selected)),
                        encoding="utf-8",
                    )
                    completion = read_canonical_json(accepted / "complete.json")
                    completion["artifacts"]["official-selected.txt"] = file_sha256(
                        selected_path
                    )
                    staging = accepted.with_name("selection-mutated")
                    accepted.rename(staging)
                    accepted = reseal_selection_root(staging, completion)
                elif mutation == 7:
                    ledger_path = accepted / "selected-files.jsonl"
                    rows = ledger_path.read_bytes().splitlines(keepends=True)
                    first = json.loads(rows[0])
                    first["bytes"] += 1
                    rows[0] = canonical_bytes(first)
                    ledger_path.write_bytes(b"".join(rows))
                    completion = read_canonical_json(accepted / "complete.json")
                    completion["artifacts"]["selected-files.jsonl"] = file_sha256(
                        ledger_path
                    )
                    staging = accepted.with_name("selection-mutated")
                    accepted.rename(staging)
                    accepted = reseal_selection_root(staging, completion)
                else:
                    with layout.benchmarks[0].open("ab") as benchmark:
                        benchmark.write(b"; physical drift\n")

                run_dir = root / "must-not-exist"
                with self.assertRaises(ContractError):
                    layout.execute(
                        run_dir,
                        runner=fixed_result,
                        official_selection_root=accepted,
                    )
                self.assertFalse(run_dir.exists())

    def test_cgroup_preflight_rejects_legacy_selection_without_fixture_override(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            layout = Layout(root)
            run = cgroup_run_manifest(
                repository_root=ROOT,
                source_root=SMTCOMP,
                file_list=layout.file_list,
                selection_manifest=layout.selection_manifest,
                corpus_manifest=layout.corpus_manifest,
                environment_manifest=layout.environment_manifest,
                solver_id="fake",
                command_template=layout.command_template,
                track="single_query",
                wall_limit_ms=layout.wall_limit_ms,
                memory_limit_bytes=layout.memory_limit_bytes,
                cores=1,
                shard_count=1,
                worker_slots=1,
                aggregate_memory_bytes=layout.memory_limit_bytes,
                pids_max=32,
            )
            layout.run_manifest.write_bytes(canonical_bytes(run))
            run_dir = root / "must-not-exist"
            with self.assertRaisesRegex(ContractError, "unadmitted selection fixture"):
                layout.execute(run_dir, runner=fixed_result)
            self.assertFalse(run_dir.exists())

    def test_benchmark_byte_drift_rejects_before_solver_or_run_directory(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            layout = Layout(root)
            layout.benchmarks[0].write_text(
                layout.benchmarks[0].read_text(encoding="utf-8") + "; drift\n",
                encoding="utf-8",
            )
            called = False

            def must_not_run(command: list[str], **kwargs) -> RunResult:
                nonlocal called
                called = True
                return fixed_result(command, **kwargs)

            run_dir = root / "must-not-start"
            with self.assertRaisesRegex(
                ContractError, "selection manifest benchmark identity mismatch"
            ):
                layout.execute(run_dir, runner=must_not_run)
            self.assertFalse(called)
            self.assertFalse(run_dir.exists())

    def test_process_kill_before_solver_start_is_accounted_on_resume(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            layout = Layout(root)
            run_dir = root / "killed-before-solver"
            marker = root / "phase.marker"

            def child() -> None:
                def pause(phase: str) -> None:
                    marker.write_text(phase + "\n", encoding="ascii")
                    signal.pause()

                layout.execute(run_dir, runner=fixed_result, phase_hook=pause)

            process = multiprocessing.get_context("fork").Process(target=child)
            process.start()
            deadline = time.monotonic() + 5
            while time.monotonic() < deadline:
                if marker.exists() and marker.read_text(encoding="ascii").strip():
                    break
                if not process.is_alive():
                    self.fail(f"fixture process exited early: {process.exitcode}")
                time.sleep(0.01)
            self.assertEqual(marker.read_text(encoding="ascii").strip(), "before_solver_start")
            process.kill()
            process.join(timeout=5)
            self.assertFalse(process.is_alive())

            lease_path = run_dir / "leases" / "0.json"
            owner = read_canonical_json(lease_path)
            recover_shard_lease(run_dir, "0", owner["owner_id"])
            self.assertTrue(layout.execute(run_dir, runner=fixed_result))
            bundle = load_bundle(run_dir)
            self.assertEqual(len(bundle.attempts["0"]), 2)
            self.assertIsNone(bundle.attempts["0"][0]["terminal"])
            self.assertEqual(
                bundle.completions["0"]["unclosed_attempt_ids"],
                [bundle.attempts["0"][0]["attempt_id"]],
            )

    def test_interrupted_resume_matches_uninterrupted_scoring_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            layout = Layout(Path(tmp))
            baseline_dir = Path(tmp) / "baseline"
            resumed_dir = Path(tmp) / "resumed"
            self.assertTrue(layout.execute(baseline_dir, runner=fixed_result))

            calls = 0

            def interrupt_second(command: list[str], **kwargs) -> RunResult:
                nonlocal calls
                calls += 1
                if calls == 2:
                    raise KeyboardInterrupt("fixture interruption")
                return fixed_result(command, **kwargs)

            with self.assertRaises(KeyboardInterrupt):
                layout.execute(resumed_dir, runner=interrupt_second)
            self.assertFalse((resumed_dir / "completions" / "0.json").exists())
            self.assertTrue(layout.execute(resumed_dir, runner=fixed_result))
            self.assertEqual(
                validate_bundle_directory(baseline_dir, require_output_sidecars=True),
                validate_bundle_directory(resumed_dir, require_output_sidecars=True),
            )
            attempts = load_bundle(resumed_dir).attempts["0"]
            self.assertEqual(len(attempts), 2)
            self.assertEqual(attempts[0]["terminal"]["status"], "failed")
            self.assertEqual(len(attempts[0]["terminal"]["new_result_keys"]), 1)
            self.assertEqual(len(attempts[1]["terminal"]["skipped_result_keys"]), 1)
            self.assertEqual(len(attempts[1]["terminal"]["new_result_keys"]), 1)

    def test_cli_retains_timeout_verdict_exports_only_after_sidecar_validation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            layout = Layout(root, hang=True)
            run_dir = root / "run"
            raw = root / "raw.json"
            completed = subprocess.run(
                layout.cli(run_dir, raw=raw),
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=10,
                check=False,
            )
            self.assertEqual(completed.returncode, 0, completed.stderr)
            self.assertTrue(raw.is_file())
            bundle = load_bundle(run_dir)
            timeout = next(
                record
                for record in bundle.records
                if record["termination_class"] == "wall-timeout"
            )
            self.assertEqual(timeout["observed_status"], "sat")
            self.assertEqual(timeout["reported_status"], "sat")
            self.assertEqual(timeout["resource_limit_kind"], "wall")
            exported = json.loads(raw.read_text(encoding="utf-8"))
            self.assertEqual(exported[str(layout.benchmarks[0])]["fake"]["reported_status"], "sat")

            sidecar = run_dir / "outputs" / "stdout" / f"{timeout['stdout_sha256']}.bin"
            sidecar.chmod(0o644)
            sidecar.write_bytes(b"mutated\n")
            with self.assertRaisesRegex(ContractError, "sidecar hash mismatch"):
                export_legacy_raw(run_dir, root / "must-not-exist.json")
            self.assertFalse((root / "must-not-exist.json").exists())

    def test_second_owner_fails_and_stale_recovery_is_explicit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            first = {
                "owner_id": "owner-one",
                "host_id": socket.gethostname(),
                "pid": os.getpid(),
            }
            acquire_shard_lease(root, "0", first)
            second = dict(first, owner_id="owner-two")
            with self.assertRaises(LeaseConflict):
                acquire_shard_lease(root, "0", second)
            with self.assertRaises(LeaseConflict):
                recover_shard_lease(root, "0", "wrong-owner")
            recovered = recover_shard_lease(root, "0", "owner-one")
            self.assertTrue(recovered.is_file())
            lease = acquire_shard_lease(root, "0", second)
            self.assertEqual(lease.owner_id, "owner-two")

    def test_process_kill_during_solver_is_accounted_on_resume(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            marker = root / "solver.pid"
            layout = Layout(root, hang=True, marker=marker)
            layout.wall_limit_ms = 1000
            layout.file_list.write_text(f"{layout.benchmarks[0]}\n", encoding="utf-8")
            layout.selection_manifest.write_bytes(
                canonical_bytes(
                    selection_input_manifest(layout.file_list, "non-incremental/")
                )
            )
            # The selected-list identity changed; rebuild the manifest before launch.
            run = fixture_run_manifest(
                repository_root=ROOT,
                source_root=SMTCOMP,
                file_list=layout.file_list,
                selection_manifest=layout.selection_manifest,
                corpus_manifest=layout.corpus_manifest,
                environment_manifest=layout.environment_manifest,
                solver_id="fake",
                command_template=layout.command_template,
                track="single_query",
                wall_limit_ms=layout.wall_limit_ms,
                memory_limit_bytes=layout.memory_limit_bytes,
                cores=1,
                shard_count=1,
            )
            layout.run_manifest.write_bytes(canonical_bytes(run))
            run_dir = root / "killed"
            process = subprocess.Popen(
                layout.cli(run_dir),
                cwd=ROOT,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
            child_pid = None
            try:
                deadline = time.monotonic() + 5
                while time.monotonic() < deadline and child_pid is None:
                    if process.poll() is not None:
                        self.fail(f"runner exited before solver marker: {process.returncode}")
                    if marker.exists():
                        marker_value = marker.read_text(encoding="ascii").strip()
                        if marker_value:
                            child_pid = int(marker_value)
                            break
                    time.sleep(0.01)
                self.assertIsNotNone(child_pid, "solver did not publish its PID")
                contender = subprocess.run(
                    layout.cli(run_dir),
                    cwd=ROOT,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    timeout=5,
                    check=False,
                )
                self.assertEqual(contender.returncode, 2, contender.stderr)
                self.assertIn("shard lease already exists", contender.stderr)
                process.kill()
                process.wait(timeout=5)
            finally:
                if child_pid is None and process.poll() is None:
                    children = subprocess.run(
                        ["pgrep", "-P", str(process.pid)],
                        stdout=subprocess.PIPE,
                        stderr=subprocess.DEVNULL,
                        text=True,
                        check=False,
                    ).stdout.split()
                    if children:
                        child_pid = int(children[0])
                if process.poll() is None:
                    process.kill()
                    process.wait(timeout=5)
                if child_pid is not None:
                    try:
                        os.killpg(child_pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass

            lease_path = run_dir / "leases" / "0.json"
            owner = read_canonical_json(lease_path)
            recover_shard_lease(run_dir, "0", owner["owner_id"])
            marker.unlink(missing_ok=True)
            resumed = subprocess.run(
                layout.cli(run_dir),
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=10,
                check=False,
            )
            self.assertEqual(resumed.returncode, 0, resumed.stderr)
            bundle = load_bundle(run_dir)
            self.assertEqual(len(bundle.attempts["0"]), 2)
            self.assertEqual(
                bundle.completions["0"]["unclosed_attempt_ids"],
                [bundle.attempts["0"][0]["attempt_id"]],
            )
            validate_bundle_directory(run_dir, require_output_sidecars=True)


if __name__ == "__main__":
    unittest.main()
