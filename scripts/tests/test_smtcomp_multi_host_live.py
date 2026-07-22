"""Opt-in destructive E3 gate across the registered s5/s6/s7 fleet."""

from __future__ import annotations

import os
import subprocess
import sys
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SMTCOMP = ROOT / "scripts" / "smtcomp_repro"
FIXTURES = SMTCOMP / "fixtures" / "e3"
sys.path.insert(0, str(SMTCOMP))

from multi_host import (  # noqa: E402
    allocation,
    build_host_command,
    build_plan,
    canonical_outcome_projection,
    environment_manifest,
    finalize_multi_host_run,
    finish_allocation,
    host_registration,
    install_host_command,
    kill_remote_launcher,
    prepare_run_directory,
    recover_failed_shard,
    remote_file_observation,
    remote_liveness,
    remote_probe,
    stage_execution_bundle,
    start_allocation,
    validate_multi_host_evidence,
)
from resume_contract import ContractError, canonical_bytes  # noqa: E402
from resume_fs import (  # noqa: E402
    atomic_install_bytes,
    atomic_install_json,
    load_bundle,
    read_canonical_json,
)
from resume_runner import (  # noqa: E402
    cgroup_run_manifest,
    export_legacy_raw,
    selection_input_manifest,
    sha256_bytes,
    sha256_file,
)


HOSTS = (("h0", "s5"), ("h1", "s6"), ("h2", "s7"))
MEMORY_BYTES = 64 * 1024**2
SHARD_COUNT = 3


class E3LiveGate(unittest.TestCase):
    def require_live_gate(self) -> None:
        if os.environ.get("AXEYUM_REQUIRE_SMTCOMP_MULTIHOST") != "1":
            self.skipTest("set AXEYUM_REQUIRE_SMTCOMP_MULTIHOST=1 for s5/s6/s7")
        status = subprocess.check_output(
            ["git", "status", "--porcelain=v1", "--untracked-files=all"],
            cwd=ROOT,
        )
        if status:
            self.fail("the required E3 gate must run from a clean committed worktree")

    def write_inputs(
        self, gate_root: Path, staged: Path, environment: dict
    ) -> tuple[dict[str, Path], list[Path]]:
        inputs = gate_root / "inputs"
        inputs.mkdir(parents=True)
        family = (
            staged
            / "scripts"
            / "smtcomp_repro"
            / "fixtures"
            / "e3"
            / "non-incremental"
            / "QF_BV"
            / "e3"
        )
        benchmarks = sorted(family.glob("case-*.smt2"))
        self.assertEqual(len(benchmarks), 6)
        paths = {
            "file_list": inputs / "selected.txt",
            "selection": inputs / "selection.json",
            "corpus": inputs / "corpus.json",
            "environment": inputs / "environment.json",
            "run": inputs / "run.json",
        }
        atomic_install_bytes(
            inputs,
            paths["file_list"].name,
            "".join(f"{path.resolve()}\n" for path in benchmarks).encode("utf-8"),
        )
        atomic_install_json(
            inputs,
            paths["selection"].name,
            selection_input_manifest(paths["file_list"], "non-incremental/"),
        )
        atomic_install_json(
            inputs,
            paths["corpus"].name,
            {
                "schema": "axeyum.smtcomp-e3-test-corpus.v1",
                "fixture_root": str(family),
                "files": [
                    {"path": str(path), "sha256": sha256_file(path)}
                    for path in benchmarks
                ],
            },
        )
        atomic_install_json(inputs, paths["environment"].name, environment)
        return paths, benchmarks

    def build_allocations(self, enforcement_id: str) -> list[dict]:
        rows = [
            allocation(
                allocation_id=f"initial-{index}",
                generation=0,
                host_id=host_id,
                shard_ids=[index],
                enforcement_id=enforcement_id,
            )
            for index, (host_id, _target) in enumerate(HOSTS)
        ]
        rows.append(
            allocation(
                allocation_id="retry-0",
                generation=1,
                host_id="h1",
                shard_ids=[0],
                enforcement_id=enforcement_id,
                recovers_allocation_id="initial-0",
            )
        )
        return rows

    def command_argv(
        self,
        *,
        staged: Path,
        paths: dict[str, Path],
        run_dir: Path,
        marker_root: Path,
        shard_id: int,
        session_id: str,
    ) -> list[str]:
        fake_solver = staged / "scripts" / "smtcomp_repro" / "fixtures" / "e3" / "fake_solver.py"
        solver = f"e3-fake=/usr/bin/python3 {fake_solver} {{bench}} {marker_root}"
        return [
            "/usr/bin/python3",
            "-B",
            str(staged / "scripts" / "smtcomp_repro" / "compete.py"),
            "--host-run",
            "--host-shards",
            str(shard_id),
            "--host-session-id",
            session_id,
            "--file-list",
            str(paths["file_list"]),
            "--solver",
            solver,
            "--track",
            "single_query",
            "--wall-limit",
            "10",
            "--mem-gb",
            "0.0625",
            "--cores",
            "1",
            "--run-manifest",
            str(paths["run"]),
            "--run-dir",
            str(run_dir),
            "--selection-manifest",
            str(paths["selection"]),
            "--corpus-manifest",
            str(paths["corpus"]),
            "--environment-manifest",
            str(paths["environment"]),
            "--source-identity-manifest",
            str(staged / "source-identity.json"),
            "--quiet",
        ]

    def install_commands(
        self,
        *,
        plan_path: Path,
        paths: dict[str, Path],
        staged: Path,
        run_dir: Path,
        marker_root: Path,
        allocation_ids: list[str],
        sessions: dict[str, str],
    ) -> dict[str, Path]:
        helper = staged / "scripts" / "smtcomp_repro" / "multi_host.py"
        plan = read_canonical_json(plan_path)
        allocations = {row["allocation_id"]: row for row in plan["allocations"]}
        installed = {}
        for allocation_id in allocation_ids:
            row = allocations[allocation_id]
            command = build_host_command(
                plan_path=plan_path,
                run_manifest_path=paths["run"],
                allocation_id=allocation_id,
                session_id=sessions[allocation_id],
                remote_helper_path=helper,
                argv=self.command_argv(
                    staged=staged,
                    paths=paths,
                    run_dir=run_dir,
                    marker_root=marker_root,
                    shard_id=row["shard_ids"][0],
                    session_id=sessions[allocation_id],
                ),
            )
            installed[allocation_id] = install_host_command(run_dir, command)
        return installed

    def wait_for_failure_point(
        self,
        run_dir: Path,
        marker: Path,
        session_id: str,
        registration: dict,
        helper: Path,
        prior_marker_mtime_ns: int,
    ) -> dict:
        deadline = time.monotonic() + 15
        preflight_path = run_dir / "resource-sessions" / session_id / "preflight.json"
        shard_attempts = run_dir / "attempts" / "0"
        while time.monotonic() < deadline:
            marker_observed = False
            try:
                marker_observed = (
                    remote_file_observation(
                        registration=registration,
                        remote_helper_path=helper,
                        path=marker,
                    )["mtime_ns"]
                    > prior_marker_mtime_ns
                )
            except ContractError:
                pass
            if marker_observed and preflight_path.is_file() and shard_attempts.is_dir():
                attempts = list(shard_attempts.glob("*.json"))
                if attempts:
                    return read_canonical_json(preflight_path)
            time.sleep(0.05)
        self.fail(
            "failed allocation did not publish marker, resource preflight, and shard attempt"
        )

    def wait_until_dead(
        self, registration: dict, helper: Path, unit: str, launcher_pid: int
    ) -> dict:
        deadline = time.monotonic() + 15
        last = None
        while time.monotonic() < deadline:
            last = remote_liveness(
                registration=registration,
                remote_helper_path=helper,
                unit=unit,
                launcher_pid=launcher_pid,
            )
            if not last["launcher_live"] and last["unit_state"] not in {
                "active",
                "activating",
                "deactivating",
            }:
                return last
            time.sleep(0.1)
        self.fail(f"registered failed unit did not become inactive: {last}")

    def test_three_host_loss_retry_matches_uninterrupted_control(self) -> None:
        self.require_live_gate()
        configured_root = Path(
            os.environ.get(
                "AXEYUM_SMTCOMP_MULTIHOST_ROOT",
                "/nas3/data/axeyum/harness/e3-gate",
            )
        )
        if not configured_root.is_absolute():
            self.fail("E3 shared root must be absolute")
        configured_root.parent.resolve(strict=True)
        configured_root.mkdir(mode=0o755, exist_ok=True)
        shared_root = configured_root.resolve(strict=True)
        if str(shared_root) != str(configured_root):
            self.fail("E3 shared root must be a canonical non-symlinked path")
        source_parent = shared_root / "source-bundles"
        source_parent.mkdir(parents=True, exist_ok=True)
        staged, source_identity = stage_execution_bundle(
            repository_root=ROOT,
            source_root=SMTCOMP,
            fixture_root=FIXTURES,
            staging_parent=source_parent,
        )
        helper = staged / "scripts" / "smtcomp_repro" / "multi_host.py"
        observations = [
            remote_probe(
                ssh_target=target,
                remote_helper_path=helper,
                shared_root=shared_root,
            )
            for _host_id, target in HOSTS
        ]
        environment = environment_manifest(observations)
        environment_sha = sha256_bytes(canonical_bytes(environment))
        registrations = [
            host_registration(
                host_id=host_id,
                ssh_target=target,
                observation=observation,
                environment_sha256=environment_sha,
            )
            for (host_id, target), observation in zip(HOSTS, observations, strict=True)
        ]
        if sha256_file(Path("/usr/bin/python3")) != observations[0][
            "python_executable_sha256"
        ]:
            self.fail("coordinator and registered hosts have different Python executable bytes")

        commit = source_identity["repository_commit"]
        stamp = f"{time.time_ns()}-{commit[:12]}"
        gate_root = shared_root / f"live-{stamp}"
        gate_root.mkdir(mode=0o755)
        marker_root = gate_root / "markers"
        marker_root.mkdir()
        paths, _benchmarks = self.write_inputs(gate_root, staged, environment)
        command_template = [
            "/usr/bin/python3",
            str(staged / "scripts" / "smtcomp_repro" / "fixtures" / "e3" / "fake_solver.py"),
            "{bench}",
            str(marker_root),
        ]
        run = cgroup_run_manifest(
            repository_root=ROOT,
            source_root=staged / "scripts" / "smtcomp_repro",
            file_list=paths["file_list"],
            selection_manifest=paths["selection"],
            corpus_manifest=paths["corpus"],
            environment_manifest=paths["environment"],
            solver_id="e3-fake",
            command_template=command_template,
            track="single_query",
            wall_limit_ms=10_000,
            memory_limit_bytes=MEMORY_BYTES,
            cores=1,
            shard_count=SHARD_COUNT,
            worker_slots=1,
            aggregate_memory_bytes=MEMORY_BYTES,
            pids_max=32,
            multi_host=True,
            source_identity=source_identity,
            toolchain_identity=observations[0]["toolchain_identity_sha256"],
        )
        atomic_install_json(paths["run"].parent, paths["run"].name, run)
        allocations = self.build_allocations(
            run["resource_enforcement"]["enforcement_id"]
        )

        evidence = {}
        completions = {}
        for mode in ("control", "loss-retry"):
            run_dir = gate_root / mode
            fault = {"kind": "none"}
            marker = marker_root / "case-a-kill.smt2.marker"
            prior_marker_mtime_ns = 0
            if mode == "loss-retry":
                prior_marker_mtime_ns = remote_file_observation(
                    registration=registrations[0],
                    remote_helper_path=helper,
                    path=marker,
                )["mtime_ns"]
                marker.unlink(missing_ok=True)
                fault = {
                    "kind": "kill-host-runner-after-marker",
                    "allocation_id": "initial-0",
                    "marker_path": str(marker),
                }
            plan = build_plan(
                run=run,
                shared_root=shared_root,
                environment_class_sha256=sha256_file(paths["environment"]),
                host_registrations=registrations,
                allocations=allocations,
                fault_injection=fault,
            )
            prepare_run_directory(plan=plan, run=run, run_dir=run_dir)
            plan_path = run_dir / "multi-host-plan.json"
            atomic_install_json(run_dir, plan_path.name, plan)
            prefix = "ctl" if mode == "control" else "loss"
            sessions = {
                "initial-0": f"{prefix}-initial-0-{commit[:8]}",
                "initial-1": f"{prefix}-initial-1-{commit[:8]}",
                "initial-2": f"{prefix}-initial-2-{commit[:8]}",
                "retry-0": f"{prefix}-retry-0-{commit[:8]}",
            }
            commands = self.install_commands(
                plan_path=plan_path,
                paths=paths,
                staged=staged,
                run_dir=run_dir,
                marker_root=marker_root,
                allocation_ids=["initial-0", "initial-1", "initial-2"],
                sessions=sessions,
            )
            handles = {
                allocation_id: start_allocation(
                    plan=plan,
                    command_manifest=commands[allocation_id],
                    run_dir=run_dir,
                )
                for allocation_id in ("initial-0", "initial-1", "initial-2")
            }
            try:
                if mode == "loss-retry":
                    preflight = self.wait_for_failure_point(
                        run_dir,
                        marker,
                        sessions["initial-0"],
                        registrations[0],
                        helper,
                        prior_marker_mtime_ns,
                    )
                    unit = (
                        f"{run['resource_enforcement']['unit_prefix']}-"
                        f"{sessions['initial-0']}.service"
                    )
                    kill_remote_launcher(
                        registration=registrations[0],
                        remote_helper_path=helper,
                        unit=unit,
                        launcher_pid=preflight["launcher_pid"],
                    )
            finally:
                terminals = {
                    allocation_id: finish_allocation(handle, timeout=30)
                    for allocation_id, handle in handles.items()
                }
            if mode == "control":
                self.assertEqual(
                    {row["status"] for row in terminals.values()}, {"completed"}
                )
            else:
                self.assertNotEqual(terminals["initial-0"]["status"], "completed")
                preflight = read_canonical_json(
                    run_dir
                    / "resource-sessions"
                    / sessions["initial-0"]
                    / "preflight.json"
                )
                unit = (
                    f"{run['resource_enforcement']['unit_prefix']}-"
                    f"{sessions['initial-0']}.service"
                )
                self.wait_until_dead(
                    registrations[0], helper, unit, preflight["launcher_pid"]
                )
                recover_failed_shard(
                    plan=plan,
                    run=run,
                    run_dir=run_dir,
                    failed_allocation_id="initial-0",
                    retry_allocation_id="retry-0",
                    resource_session_id=sessions["initial-0"],
                    remote_helper_path=helper,
                )
                retry_command = self.install_commands(
                    plan_path=plan_path,
                    paths=paths,
                    staged=staged,
                    run_dir=run_dir,
                    marker_root=marker_root,
                    allocation_ids=["retry-0"],
                    sessions=sessions,
                )["retry-0"]
                retry = start_allocation(
                    plan=plan,
                    command_manifest=retry_command,
                    run_dir=run_dir,
                )
                retry_terminal = finish_allocation(retry, timeout=30)
                self.assertEqual(retry_terminal["status"], "completed")
            completion = finalize_multi_host_run(run_dir)
            validate_multi_host_evidence(run_dir, load_bundle(run_dir))
            export_legacy_raw(run_dir, gate_root / f"{mode}-raw.json")
            evidence[mode] = run_dir
            completions[mode] = completion

        self.assertEqual(
            canonical_outcome_projection(evidence["control"]),
            canonical_outcome_projection(evidence["loss-retry"]),
        )
        self.assertEqual(completions["control"]["unclosed_allocation_attempt_ids"], [])
        self.assertEqual(
            completions["loss-retry"]["unclosed_allocation_attempt_ids"], []
        )
        loss_resources = read_canonical_json(
            evidence["loss-retry"] / "resource-completion.json"
        )
        self.assertEqual(
            loss_resources["unclosed_session_ids"],
            [f"loss-initial-0-{commit[:8]}"],
        )
        shard_completion = read_canonical_json(
            evidence["loss-retry"] / "completions" / "0.json"
        )
        self.assertEqual(len(shard_completion["unclosed_attempt_ids"]), 1)
        recoveries = list(
            (evidence["loss-retry"] / "multi-host-recoveries").glob("*.json")
        )
        self.assertEqual(len(recoveries), 1)
        print(
            f"E3_LIVE_EVIDENCE={gate_root}\n"
            f"E3_CONTROL_COMPLETION={completions['control']['record_sha256']}\n"
            f"E3_LOSS_COMPLETION={completions['loss-retry']['record_sha256']}",
            file=sys.stderr,
        )
if __name__ == "__main__":
    unittest.main()
