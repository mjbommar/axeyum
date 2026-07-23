"""Portable E3 plan, transport, command, and exact-recovery gates."""

from __future__ import annotations

import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SMTCOMP = ROOT / "scripts" / "smtcomp_repro"
FIXTURES = SMTCOMP / "fixtures" / "e3"
sys.path.insert(0, str(SMTCOMP))

from multi_host import (  # noqa: E402
    ALLOCATION_SCHEMA,
    ATTEMPT_SCHEMA,
    PLAN_SCHEMA,
    REGISTRATION_SCHEMA,
    TERMINAL_SCHEMA as ALLOCATION_TERMINAL_SCHEMA,
    TRANSPORT,
    allocation,
    build_host_command,
    build_multi_host_completion,
    install_host_command,
    recover_failed_shard,
    recover_released_failed_shard,
    stage_execution_bundle,
    validate_execution_bundle,
    validate_host_command,
    validate_multi_host_state,
    validate_plan,
)
from resource_enforcement import (  # noqa: E402
    MULTI_HOST_KIND,
    PREFLIGHT_SCHEMA,
    TERMINAL_SCHEMA as RESOURCE_TERMINAL_SCHEMA,
    build_resource_completion,
    install_resource_completion,
)
from resume_contract import ContractError, canonical_bytes, digest  # noqa: E402
from resume_fs import (  # noqa: E402
    atomic_install_bytes,
    atomic_install_json,
    load_bundle,
    read_canonical_json,
)
from resume_runner import (  # noqa: E402
    cgroup_run_manifest,
    execute_resumable,
    export_legacy_raw,
    selection_input_manifest,
    sha256_bytes,
    sha256_file,
)
from runner import RunResult  # noqa: E402
from scoring import Status  # noqa: E402


def seal(value: dict, field: str = "record_sha256") -> dict:
    result = copy.deepcopy(value)
    result.pop(field, None)
    result[field] = digest(result)
    return result


class PortableE3:
    def __init__(self, root: Path):
        self.root = root.resolve()
        self.root.mkdir(parents=True, exist_ok=True)
        self.environment_sha = "d" * 64
        self.filesystem_sha = "c" * 64
        self.enforcement_id = "b" * 64
        self.run = {
            "identity_sha256": "a" * 64,
            "identity": {
                "shard_count": 3,
                "repository_commit": "fixture",
                "source_tree_state_sha256": "e" * 64,
                "runner_source_sha256": "f" * 64,
            },
            "resource_enforcement": {
                "kind": MULTI_HOST_KIND,
                "enforcement_id": self.enforcement_id,
                "unit_prefix": "axeyum-smtcomp-e3",
            },
        }
        self.registrations = [self.registration(index) for index in range(3)]
        self.allocations = [
            allocation(
                allocation_id=f"initial-{index}",
                generation=0,
                host_id=f"h{index}",
                shard_ids=[index],
                enforcement_id=self.enforcement_id,
            )
            for index in range(3)
        ]
        self.allocations.append(
            allocation(
                allocation_id="retry-0",
                generation=1,
                host_id="h1",
                shard_ids=[0],
                enforcement_id=self.enforcement_id,
                recovers_allocation_id="initial-0",
            )
        )

    def registration(self, index: int) -> dict:
        return seal(
            {
                "schema": REGISTRATION_SCHEMA,
                "host_id": f"h{index}",
                "ssh_target": f"s{index + 5}",
                "hostname": f"server{index + 5}",
                "kernel_release": "7.0.0-test",
                "machine": "x86_64",
                "python_version": "3.14.4",
                "python_executable_sha256": "1" * 64,
                "toolchain_identity_sha256": "2" * 64,
                "cgroup_controllers": ["cpu", "io", "memory", "pids"],
                "user_systemd_transient": True,
                "shared_filesystem_class_sha256": self.filesystem_sha,
                "environment_class_sha256": self.environment_sha,
            }
        )

    def plan(self, *, fault: dict | None = None) -> dict:
        return seal(
            {
                "schema": PLAN_SCHEMA,
                "run_identity_sha256": self.run["identity_sha256"],
                "transport": TRANSPORT,
                "shared_root": str(self.root),
                "shared_filesystem_class_sha256": self.filesystem_sha,
                "environment_class_sha256": self.environment_sha,
                "host_registrations": self.registrations,
                "allocations": self.allocations,
                "fault_injection": fault or {"kind": "none"},
            },
            "plan_sha256",
        )


class MultiHostPortableTests(unittest.TestCase):
    @staticmethod
    def snapshot(run: dict, session_id: str, pid: int) -> dict:
        resources = run["resource_enforcement"]
        return {
            "cgroup_path": f"/fixture/{resources['unit_prefix']}-{session_id}.service",
            "cgroup_inode": 1000 + pid,
            "controllers": ["cpu", "memory", "pids"],
            "cgroup_type": "domain",
            "memory_max_bytes": resources["aggregate_memory_bytes"],
            "memory_swap_max_bytes": resources["memory_swap_bytes"],
            "memory_oom_group": resources["memory_oom_group"],
            "memory_peak_bytes": 1024,
            "memory_events": {"oom": 0, "oom_kill": 0},
            "cpu_quota_usec": resources["aggregate_cpu_quota_usec"],
            "cpu_period_usec": resources["cpu_period_usec"],
            "cpu_stat": {"usage_usec": 1},
            "pids_max": resources["pids_max"],
            "pids_current": 1,
            "pids_peak": 1,
            "pids_events": {"max": 0},
            "member_pids": [pid],
        }

    @staticmethod
    def solver_result(command: list[str], **_kwargs) -> RunResult:
        benchmark = next(token for token in command if token.endswith(".smt2"))
        unsat = Path(benchmark).name in {"case-b.smt2", "case-d.smt2", "case-f.smt2"}
        status = Status.UNSAT if unsat else Status.SAT
        output = f"{status.value}\n".encode("ascii")
        return RunResult(
            reported=status,
            observed=status,
            wall_time=0.001,
            scoring_wall_time=0.001,
            runner_elapsed=0.001,
            cpu_time=0.0005,
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

    def test_plan_requires_three_distinct_equivalent_hosts_and_exact_partition(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            layout = PortableE3(Path(tmp))
            validate_plan(layout.plan(), layout.run, inspect_shared_root=False)

            mutations: list[tuple[str, object, str]] = [
                (
                    "two hosts",
                    lambda plan: plan["host_registrations"].pop(),
                    "three registrations",
                ),
                (
                    "duplicate host",
                    lambda plan: plan["host_registrations"].__setitem__(
                        1, plan["host_registrations"][0]
                    ),
                    "duplicate multi-host registration",
                ),
                (
                    "overlap",
                    lambda plan: plan["allocations"][1].__setitem__("shard_ids", [0]),
                    "partition every shard",
                ),
                (
                    "missing shard",
                    lambda plan: plan["allocations"].pop(2),
                    "partition every shard",
                ),
                (
                    "unknown retry host",
                    lambda plan: plan["allocations"][3].__setitem__("host_id", "h9"),
                    "unregistered host",
                ),
                (
                    "same-host retry",
                    lambda plan: plan["allocations"][3].__setitem__("host_id", "h0"),
                    "move to another host",
                ),
            ]
            for name, mutate, message in mutations:
                with self.subTest(name=name):
                    plan = copy.deepcopy(layout.plan())
                    mutate(plan)
                    for index, row in enumerate(plan["allocations"]):
                        if row.get("record_sha256") != digest(
                            {key: value for key, value in row.items() if key != "record_sha256"}
                        ):
                            plan["allocations"][index] = seal(row)
                    plan = seal(plan, "plan_sha256")
                    with self.assertRaisesRegex(ContractError, message):
                        validate_plan(plan, layout.run, inspect_shared_root=False)

    def test_fault_marker_must_be_bounded_and_environment_drift_rejects(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            layout = PortableE3(Path(tmp))
            marker = layout.root / "markers" / "case.marker"
            valid = layout.plan(
                fault={
                    "kind": "kill-host-runner-after-marker",
                    "allocation_id": "initial-0",
                    "marker_path": str(marker),
                }
            )
            validate_plan(valid, layout.run, inspect_shared_root=False)

            escaped = copy.deepcopy(valid)
            escaped["fault_injection"]["marker_path"] = "/tmp/escape.marker"
            escaped = seal(escaped, "plan_sha256")
            with self.assertRaisesRegex(ContractError, "escapes"):
                validate_plan(escaped, layout.run, inspect_shared_root=False)

            drift = copy.deepcopy(layout.plan())
            drift["host_registrations"][1]["kernel_release"] = "different"
            drift["host_registrations"][1] = seal(drift["host_registrations"][1])
            drift = seal(drift, "plan_sha256")
            with self.assertRaisesRegex(ContractError, "environment class"):
                validate_plan(drift, layout.run, inspect_shared_root=False)

    def test_content_addressed_bundle_rejects_tamper_and_extra_namespace(self) -> None:
        for mutation in ("content", "extra"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as tmp:
                staging = Path(tmp)
                bundle, _source = stage_execution_bundle(
                    repository_root=ROOT,
                    source_root=SMTCOMP,
                    fixture_root=FIXTURES,
                    staging_parent=staging,
                )
                validate_execution_bundle(bundle)
                if mutation == "content":
                    target = bundle / "scripts" / "smtcomp_repro" / "compete.py"
                    target.chmod(0o644)
                    target.write_bytes(target.read_bytes() + b"# drift\n")
                    message = "runner digest mismatch|file mismatch"
                else:
                    target = bundle / "unexpected.txt"
                    target.write_text("drift\n", encoding="utf-8")
                    message = "namespace mismatch"
                with self.assertRaisesRegex(ContractError, message):
                    validate_execution_bundle(bundle)

    def test_host_command_binds_allocation_and_staged_source(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            staged, source = stage_execution_bundle(
                repository_root=ROOT,
                source_root=SMTCOMP,
                fixture_root=FIXTURES,
                staging_parent=root,
            )
            layout = PortableE3(root)
            layout.run["identity"].update(
                {
                    "repository_commit": source["repository_commit"],
                    "source_tree_state_sha256": source["source_tree_state_sha256"],
                    "runner_source_sha256": source["runner_source_sha256"],
                }
            )
            plan = layout.plan()
            inputs = root / "inputs"
            inputs.mkdir()
            paths = {}
            for name in ("selected.txt", "selection.json", "corpus.json", "environment.json"):
                paths[name] = inputs / name
                paths[name].write_text("{}\n", encoding="utf-8")
            plan_path = root / "plan.json"
            run_path = root / "run.json"
            plan_path.write_bytes(canonical_bytes(plan))
            run_path.write_bytes(canonical_bytes(layout.run))
            run_dir = root / "evidence"
            argv = [
                sys.executable,
                "-B",
                str(staged / "scripts" / "smtcomp_repro" / "compete.py"),
                "--host-run",
                "--host-shards",
                "0",
                "--host-session-id",
                "session-0",
                "--run-manifest",
                str(run_path),
                "--run-dir",
                str(run_dir),
                "--file-list",
                str(paths["selected.txt"]),
                "--selection-manifest",
                str(paths["selection.json"]),
                "--allow-unadmitted-selection-fixture",
                "--corpus-manifest",
                str(paths["corpus.json"]),
                "--environment-manifest",
                str(paths["environment.json"]),
                "--source-identity-manifest",
                str(staged / "source-identity.json"),
            ]
            command = build_host_command(
                plan_path=plan_path,
                run_manifest_path=run_path,
                allocation_id="initial-0",
                session_id="session-0",
                remote_helper_path=staged / "scripts" / "smtcomp_repro" / "multi_host.py",
                argv=argv,
                inspect_shared_root=False,
            )
            validate_host_command(command, inspect_shared_root=False)

            drift = copy.deepcopy(command)
            shard_index = drift["argv"].index("--host-shards") + 1
            drift["argv"][shard_index] = "1"
            drift["argv_sha256"] = digest(drift["argv"])
            drift = seal(drift)
            with self.assertRaisesRegex(ContractError, "host-shards"):
                validate_host_command(drift, inspect_shared_root=False)

    def test_recovery_requires_dead_exact_owner_and_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            layout = PortableE3(Path(tmp))
            plan = layout.plan()
            session_id = "failed-session"
            session = layout.root / "resource-sessions" / session_id
            session.mkdir(parents=True)
            session.joinpath("preflight.json").write_bytes(
                canonical_bytes(
                    {
                        "host_id": "server5",
                        "shard_ids": [0],
                        "launcher_pid": 4242,
                        "run_identity_sha256": layout.run["identity_sha256"],
                        "started_at_ns": 1,
                    }
                )
            )
            leases = layout.root / "leases"
            leases.mkdir()
            leases.joinpath("0.json").write_bytes(
                canonical_bytes({"owner_id": "lease-owner"})
            )
            dead = {
                "unit": "axeyum-smtcomp-e3-failed-session.service",
                "unit_state": "failed",
                "launcher_pid": 4242,
                "launcher_live": False,
            }
            with mock.patch("multi_host.remote_liveness", return_value=dead):
                record = recover_failed_shard(
                    plan=plan,
                    run=layout.run,
                    run_dir=layout.root,
                    failed_allocation_id="initial-0",
                    retry_allocation_id="retry-0",
                    resource_session_id=session_id,
                    remote_helper_path=layout.root / "multi_host.py",
                    inspect_shared_root=False,
                )
                replay = recover_failed_shard(
                    plan=plan,
                    run=layout.run,
                    run_dir=layout.root,
                    failed_allocation_id="initial-0",
                    retry_allocation_id="retry-0",
                    resource_session_id=session_id,
                    remote_helper_path=layout.root / "multi_host.py",
                    inspect_shared_root=False,
                )
            self.assertEqual(record, replay)
            self.assertFalse((leases / "0.json").exists())
            self.assertTrue((layout.root / record["quarantine_path"]).is_file())

            retry_one = allocation(
                allocation_id="retry-1",
                generation=1,
                host_id="h2",
                shard_ids=[1],
                enforcement_id=layout.enforcement_id,
                recovers_allocation_id="initial-1",
            )
            active_plan = copy.deepcopy(plan)
            active_plan["allocations"].append(retry_one)
            active_plan = seal(active_plan, "plan_sha256")
            second_session_id = "live-session"
            second_session = layout.root / "resource-sessions" / second_session_id
            second_session.mkdir()
            second_session.joinpath("preflight.json").write_bytes(
                canonical_bytes(
                    {
                        "host_id": "server6",
                        "shard_ids": [1],
                        "launcher_pid": 4343,
                        "run_identity_sha256": layout.run["identity_sha256"],
                        "started_at_ns": 1,
                    }
                )
            )
            second = leases / "1.json"
            second.write_bytes(canonical_bytes({"owner_id": "live-owner"}))
            active = dict(dead, unit_state="active", launcher_live=True)
            with mock.patch("multi_host.remote_liveness", return_value=active):
                with self.assertRaisesRegex(ContractError, "still live"):
                    recover_failed_shard(
                        plan=active_plan,
                        run=layout.run,
                        run_dir=layout.root,
                        failed_allocation_id="initial-1",
                        retry_allocation_id="retry-1",
                        resource_session_id=second_session_id,
                        remote_helper_path=layout.root / "multi_host.py",
                        inspect_shared_root=False,
                    )
            self.assertTrue(second.is_file())

    def test_released_failed_runner_authorizes_exact_retry_without_fake_lease(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            layout = PortableE3(Path(tmp))
            plan = layout.plan()
            session_id = "failed-session"
            session = layout.root / "resource-sessions" / session_id
            session.mkdir(parents=True)
            session.joinpath("preflight.json").write_bytes(
                canonical_bytes(
                    {
                        "host_id": "server5",
                        "shard_ids": [0],
                        "launcher_pid": 4242,
                        "run_identity_sha256": layout.run["identity_sha256"],
                        "started_at_ns": 1,
                    }
                )
            )
            runner_terminal = {
                "status": "failed",
                "completed_count": 0,
                "durable_result_keys": [],
                "new_result_keys": [],
                "skipped_result_keys": [],
            }
            runner_terminal_path = layout.root / "terminals" / "0" / "runner.json"
            runner_terminal_path.parent.mkdir(parents=True)
            runner_terminal_path.write_bytes(canonical_bytes(runner_terminal))
            (layout.root / "records").mkdir()
            failed_attempt = {
                "attempt_id": "failed-attempt",
                "allocation_id": "initial-0",
                "session_id": session_id,
            }
            failed_terminal = seal(
                {
                    "schema": ALLOCATION_TERMINAL_SCHEMA,
                    "attempt_id": "failed-attempt",
                    "status": "failed",
                    "exit_code": 2,
                    "stdout_sha256": "0" * 64,
                    "stdout_bytes": 0,
                    "stderr_sha256": "1" * 64,
                    "stderr_bytes": 1,
                    "ended_at_ns": 2,
                }
            )
            attempt_path = (
                layout.root
                / "multi-host-attempts"
                / "initial-0"
                / "failed-attempt.json"
            )
            terminal_path = (
                layout.root
                / "multi-host-terminals"
                / "initial-0"
                / "failed-attempt.json"
            )
            attempt_path.parent.mkdir(parents=True)
            terminal_path.parent.mkdir(parents=True)
            attempt_path.write_bytes(canonical_bytes(failed_attempt))
            terminal_path.write_bytes(canonical_bytes(failed_terminal))
            dead = {
                "unit": "axeyum-smtcomp-e3-failed-session.service",
                "unit_state": "failed",
                "launcher_pid": 4242,
                "launcher_live": False,
            }
            allocation_evidence = (
                {},
                {"initial-0": [failed_attempt]},
                {"failed-attempt": failed_terminal},
            )
            with (
                mock.patch("multi_host.remote_liveness", return_value=dead),
                mock.patch(
                    "multi_host._load_allocation_evidence",
                    return_value=allocation_evidence,
                ),
            ):
                record = recover_released_failed_shard(
                    plan=plan,
                    run=layout.run,
                    run_dir=layout.root,
                    failed_allocation_id="initial-0",
                    retry_allocation_id="retry-0",
                    resource_session_id=session_id,
                    remote_helper_path=layout.root / "multi_host.py",
                    inspect_shared_root=False,
                )
                replay = recover_released_failed_shard(
                    plan=plan,
                    run=layout.run,
                    run_dir=layout.root,
                    failed_allocation_id="initial-0",
                    retry_allocation_id="retry-0",
                    resource_session_id=session_id,
                    remote_helper_path=layout.root / "multi_host.py",
                    inspect_shared_root=False,
                )
            self.assertEqual(record, replay)
            self.assertEqual(record["lease_state"], "released-after-failure")
            self.assertFalse((layout.root / "leases" / "0.json").exists())

            revived = dict(dead, unit_state="active", launcher_live=True)
            with (
                mock.patch("multi_host.remote_liveness", return_value=revived),
                mock.patch(
                    "multi_host._load_allocation_evidence",
                    return_value=allocation_evidence,
                ),
                self.assertRaisesRegex(ContractError, "still live"),
            ):
                recover_released_failed_shard(
                    plan=plan,
                    run=layout.run,
                    run_dir=layout.root,
                    failed_allocation_id="initial-0",
                    retry_allocation_id="retry-0",
                    resource_session_id=session_id,
                    remote_helper_path=layout.root / "multi_host.py",
                    inspect_shared_root=False,
                )

    def test_complete_portable_evidence_blocks_unaccounted_loss_and_raw_export(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            staged, source = stage_execution_bundle(
                repository_root=ROOT,
                source_root=SMTCOMP,
                fixture_root=FIXTURES,
                staging_parent=root,
            )
            source_root = staged / "scripts" / "smtcomp_repro"
            family = (
                source_root
                / "fixtures"
                / "e3"
                / "non-incremental"
                / "QF_BV"
                / "e3"
            )
            benchmarks = sorted(family.glob("case-[abc].smt2"))
            self.assertEqual(len(benchmarks), 2)
            benchmarks.insert(0, family / "case-a-kill.smt2")
            inputs = root / "inputs"
            inputs.mkdir()
            file_list = inputs / "selected.txt"
            file_list.write_text(
                "".join(f"{path}\n" for path in benchmarks), encoding="utf-8"
            )
            selection = inputs / "selection.json"
            selection.write_bytes(
                canonical_bytes(selection_input_manifest(file_list, "non-incremental/"))
            )
            corpus = inputs / "corpus.json"
            corpus.write_bytes(b'{"schema":"portable-e3-corpus"}\n')
            environment = inputs / "environment.json"
            environment.write_bytes(b'{"schema":"portable-e3-environment"}\n')
            command_template = [
                sys.executable,
                str(source_root / "fixtures" / "e3" / "fake_solver.py"),
                "{bench}",
            ]
            run = cgroup_run_manifest(
                repository_root=ROOT,
                source_root=source_root,
                file_list=file_list,
                selection_manifest=selection,
                corpus_manifest=corpus,
                environment_manifest=environment,
                solver_id="portable-e3",
                command_template=command_template,
                track="single_query",
                wall_limit_ms=1000,
                memory_limit_bytes=64 * 1024**2,
                cores=1,
                shard_count=3,
                worker_slots=1,
                aggregate_memory_bytes=64 * 1024**2,
                pids_max=32,
                multi_host=True,
                source_identity=source,
            )
            run_manifest = inputs / "run.json"
            run_manifest.write_bytes(canonical_bytes(run))
            run_dir = root / "evidence"
            sessions = ["portable-session-0", "portable-session-1", "portable-session-2"]
            for shard_id, session_id in enumerate(sessions):
                snapshot = self.snapshot(run, session_id, 100 + shard_id)
                with mock.patch("resume_runner.cgroup_snapshot", return_value=snapshot):
                    execute_resumable(
                        run_manifest=run_manifest,
                        run_dir=run_dir,
                        repository_root=ROOT,
                        source_root=source_root,
                        file_list=file_list,
                        selection_manifest=selection,
                        corpus_manifest=corpus,
                        environment_manifest=environment,
                        solver_id="portable-e3",
                        command_template=command_template,
                        track="single_query",
                        wall_limit_ms=1000,
                        memory_limit_bytes=64 * 1024**2,
                        cores=1,
                        shard_index=shard_id,
                        shard_count=3,
                        benchmark_id_marker="non-incremental/",
                        verbose=False,
                        resource_session_id=session_id,
                        source_identity_manifest=staged / "source-identity.json",
                        allow_unadmitted_selection_fixture=True,
                        runner=self.solver_result,
                    )

            environment_sha = sha256_file(environment)
            filesystem_sha = "c" * 64
            registrations = []
            for index in range(3):
                registrations.append(
                    seal(
                        {
                            "schema": REGISTRATION_SCHEMA,
                            "host_id": f"h{index}",
                            "ssh_target": f"s{index + 5}",
                            "hostname": f"server{index + 5}",
                            "kernel_release": "7.0.0-test",
                            "machine": "x86_64",
                            "python_version": "3.14.4",
                            "python_executable_sha256": "1" * 64,
                            "toolchain_identity_sha256": "2" * 64,
                            "cgroup_controllers": ["cpu", "memory", "pids"],
                            "user_systemd_transient": True,
                            "shared_filesystem_class_sha256": filesystem_sha,
                            "environment_class_sha256": environment_sha,
                        }
                    )
                )
            allocations = [
                allocation(
                    allocation_id=f"initial-{index}",
                    generation=0,
                    host_id=f"h{index}",
                    shard_ids=[index],
                    enforcement_id=run["resource_enforcement"]["enforcement_id"],
                )
                for index in range(3)
            ]
            plan = seal(
                {
                    "schema": PLAN_SCHEMA,
                    "run_identity_sha256": run["identity_sha256"],
                    "transport": TRANSPORT,
                    "shared_root": str(root),
                    "shared_filesystem_class_sha256": filesystem_sha,
                    "environment_class_sha256": environment_sha,
                    "host_registrations": registrations,
                    "allocations": allocations,
                    "fault_injection": {"kind": "none"},
                },
                "plan_sha256",
            )
            validate_plan(plan, run, inspect_shared_root=False)
            plan_path = run_dir / "multi-host-plan.json"
            atomic_install_json(run_dir, plan_path.name, plan)

            empty_sha = sha256_bytes(b"")
            for stream in ("stdout", "stderr"):
                atomic_install_bytes(
                    run_dir / "multi-host-outputs" / stream,
                    f"{empty_sha}.bin",
                    b"",
                )
            command_records = {}
            for index, session_id in enumerate(sessions):
                argv = [
                    sys.executable,
                    "-B",
                    str(source_root / "compete.py"),
                    "--host-run",
                    "--host-shards",
                    str(index),
                    "--host-session-id",
                    session_id,
                    "--run-manifest",
                    str(run_manifest),
                    "--run-dir",
                    str(run_dir),
                    "--file-list",
                    str(file_list),
                    "--selection-manifest",
                    str(selection),
                    "--allow-unadmitted-selection-fixture",
                    "--corpus-manifest",
                    str(corpus),
                    "--environment-manifest",
                    str(environment),
                    "--source-identity-manifest",
                    str(staged / "source-identity.json"),
                ]
                command = build_host_command(
                    plan_path=plan_path,
                    run_manifest_path=run_manifest,
                    allocation_id=f"initial-{index}",
                    session_id=session_id,
                    remote_helper_path=source_root / "multi_host.py",
                    argv=argv,
                    inspect_shared_root=False,
                )
                install_host_command(run_dir, command)
                command_records[index] = command

                pid = 100 + index
                snapshot = self.snapshot(run, session_id, pid)
                preflight = seal(
                    {
                        "schema": PREFLIGHT_SCHEMA,
                        "session_id": session_id,
                        "run_identity_sha256": run["identity_sha256"],
                        "enforcement_id": run["resource_enforcement"]["enforcement_id"],
                        "environment_class_sha256": environment_sha,
                        "host_id": f"server{index + 5}",
                        "shard_ids": [index],
                        "launcher_pid": pid,
                        "started_at_ns": 10 + index,
                        "snapshot": snapshot,
                    }
                )
                terminal = seal(
                    {
                        "schema": RESOURCE_TERMINAL_SCHEMA,
                        "session_id": session_id,
                        "run_identity_sha256": run["identity_sha256"],
                        "enforcement_id": run["resource_enforcement"]["enforcement_id"],
                        "status": "completed",
                        "worker_exit_codes": [0],
                        "memory_peak_bytes": 2048,
                        "pids_peak": 2,
                        "memory_events_delta": {"oom": 0, "oom_kill": 0},
                        "cpu_stat_delta": {"usage_usec": 1},
                        "pids_events_delta": {"max": 0},
                        "ended_at_ns": 20 + index,
                    }
                )
                session_dir = run_dir / "resource-sessions" / session_id
                atomic_install_json(session_dir, "preflight.json", preflight)
                atomic_install_json(session_dir, "terminal.json", terminal)

                attempt_id = f"allocation-attempt-{index}"
                launch = seal(
                    {
                        "schema": ATTEMPT_SCHEMA,
                        "plan_sha256": plan["plan_sha256"],
                        "run_identity_sha256": run["identity_sha256"],
                        "allocation_id": f"initial-{index}",
                        "attempt_id": attempt_id,
                        "host_id": f"h{index}",
                        "session_id": session_id,
                        "command_sha256": command["record_sha256"],
                        "coordinator_host": "coordinator",
                        "coordinator_pid": 99,
                        "started_at_ns": 1 + index,
                    }
                )
                allocation_terminal = seal(
                    {
                        "schema": ALLOCATION_TERMINAL_SCHEMA,
                        "attempt_id": attempt_id,
                        "status": "completed",
                        "exit_code": 0,
                        "stdout_sha256": empty_sha,
                        "stdout_bytes": 0,
                        "stderr_sha256": empty_sha,
                        "stderr_bytes": 0,
                        "ended_at_ns": 30 + index,
                    }
                )
                atomic_install_json(
                    run_dir / "multi-host-attempts" / f"initial-{index}",
                    f"{attempt_id}.json",
                    launch,
                )
                atomic_install_json(
                    run_dir / "multi-host-terminals" / f"initial-{index}",
                    f"{attempt_id}.json",
                    allocation_terminal,
                )

            install_resource_completion(
                run_dir, build_resource_completion(run=run, run_dir=run_dir)
            )
            completion = build_multi_host_completion(
                run_dir, inspect_shared_root=False
            )
            atomic_install_json(run_dir, "multi-host-completion.json", completion)
            validate_multi_host_state(
                run_dir,
                load_bundle(run_dir),
                require_completion=True,
                inspect_shared_root=False,
            )

            raw = root / "portable-raw.json"
            with mock.patch(
                "multi_host.validate_multi_host_evidence",
                side_effect=lambda path, bundle: validate_multi_host_state(
                    path,
                    bundle,
                    require_completion=True,
                    inspect_shared_root=False,
                ),
            ):
                export_legacy_raw(run_dir, raw)
            self.assertTrue(raw.is_file())

            terminal_path = (
                run_dir
                / "multi-host-terminals"
                / "initial-0"
                / "allocation-attempt-0.json"
            )
            terminal_bytes = terminal_path.read_bytes()
            terminal_path.unlink()
            with self.assertRaisesRegex(ContractError, "lacks exact recovery"):
                validate_multi_host_state(
                    run_dir,
                    load_bundle(run_dir),
                    require_completion=False,
                    inspect_shared_root=False,
                )
            atomic_install_bytes(terminal_path.parent, terminal_path.name, terminal_bytes)

            completion_path = run_dir / "multi-host-completion.json"
            completion_bytes = completion_path.read_bytes()
            completion_path.unlink()
            with mock.patch(
                "multi_host.validate_multi_host_evidence",
                side_effect=lambda path, bundle: validate_multi_host_state(
                    path,
                    bundle,
                    require_completion=True,
                    inspect_shared_root=False,
                ),
            ):
                with self.assertRaises(ContractError):
                    export_legacy_raw(run_dir, root / "must-not-export.json")
            atomic_install_bytes(completion_path.parent, completion_path.name, completion_bytes)


if __name__ == "__main__":
    unittest.main()
