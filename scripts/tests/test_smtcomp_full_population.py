"""Fixture gates for the credited SMT-COMP full-population contracts."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SMTCOMP = ROOT / "scripts" / "smtcomp_repro"
sys.path.insert(0, str(SMTCOMP))

from full_population import (  # noqa: E402
    HOST_IDS,
    INITIAL_ALLOCATION_COUNT,
    POPULATION_COUNT,
    RETRY_ALLOCATION_COUNT,
    SHARD_COUNT,
    SOLVER_IDS,
    WAVE_COUNT,
    build_population_contract,
    build_schedule,
    build_thermal_observation,
    build_thermal_stop,
    build_wave_checkpoint,
    cumulative_benchmark_count,
    scheduler_decision,
    shard_benchmark_count,
    validate_population_contract,
    validate_schedule,
    validate_thermal_observation,
    validate_thermal_stop,
    validate_wave_checkpoint,
)
from full_admission import (  # noqa: E402
    build_full_cell_admission,
    build_full_preparation_acceptance,
    validate_full_cell_admission,
)
from full_prepare import (  # noqa: E402
    FullSolverCell,
    compose_full_cell_manifests,
    full_host_argv,
    materialize_full_selection,
    publish_full_preparation_candidate,
    validate_full_cell_composition,
    validate_full_preparation,
    validate_full_selection,
)
from full_execute import WaveHandle, supervise_one_wave  # noqa: E402
import full_prepare as full_prepare_module  # noqa: E402
from full_preflight import (  # noqa: E402
    PREFLIGHT_MAX_AGE_NS,
    build_full_preflight,
    validate_full_preflight,
)
from full_readiness import (  # noqa: E402
    DEFAULT_REQUIRED_PATHS,
    build_gate_observation,
    build_readiness,
    validate_readiness,
)
from incident_sentinels import (  # noqa: E402
    SENTINEL_ROWS,
    SENTINEL_SCHEMA,
    SOLVER_ENVIRONMENT,
    seal_sentinel,
)
import multi_host as multi_host_module  # noqa: E402
from multi_host import (  # noqa: E402
    OBSERVATION_SCHEMA,
    PLAN_SCHEMA,
    REGISTRATION_SCHEMA,
    TRANSPORT,
    build_allocation_scheduler_state,
    stop_remote_unit,
    stage_execution_bundle,
    environment_manifest,
    host_registration,
    validate_plan,
)
from resource_enforcement import MULTI_HOST_KIND  # noqa: E402
from resume_contract import ContractError, canonical_bytes, digest  # noqa: E402
from resume_fs import read_canonical_json  # noqa: E402


ENFORCEMENT_ID = "e" * 64
PLAN_ID = "a" * 64
RUN_ID = "b" * 64
CELL_ID = "axeyum"
UNIT_PREFIX = "axeyum-smtcomp-full"


def reseal(value: dict) -> dict:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def seal_as(value: dict, field: str) -> dict:
    result = copy.deepcopy(value)
    result.pop(field, None)
    result[field] = digest(result)
    return result


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def scheduler_state(
    schedule: dict,
    *,
    open_attempt_ids: list[str] | None = None,
    completed_allocation_ids: list[str] | None = None,
    failed_allocation_ids: list[str] | None = None,
    lost_allocation_ids: list[str] | None = None,
) -> dict:
    opens = [] if open_attempt_ids is None else open_attempt_ids
    completed = [] if completed_allocation_ids is None else completed_allocation_ids
    failed = [] if failed_allocation_ids is None else failed_allocation_ids
    lost = [] if lost_allocation_ids is None else lost_allocation_ids
    initial_ids = [
        row["allocation_id"]
        for row in schedule["allocations"]
        if row["generation"] == 0
    ]
    rows = []
    used = set(completed + failed + lost)
    available = [value for value in initial_ids if value not in used]
    for index, attempt_id in enumerate(opens):
        rows.append(
            {
                "allocation_id": available[index],
                "attempt_id": attempt_id,
                "attempt_record_sha256": f"{index + 1:064x}",
                "terminal_status": None,
                "terminal_record_sha256": None,
            }
        )
    for index, (status, allocation_id) in enumerate(
        [("completed", value) for value in completed]
        + [("failed", value) for value in failed]
        + [("lost", value) for value in lost],
        start=len(rows) + 1,
    ):
        rows.append(
            {
                "allocation_id": allocation_id,
                "attempt_id": f"{allocation_id}-{status}",
                "attempt_record_sha256": f"{index:064x}",
                "terminal_status": status,
                "terminal_record_sha256": f"{index + 100:064x}",
            }
        )
    return build_allocation_scheduler_state(
        plan_sha256=PLAN_ID,
        run_identity_sha256=RUN_ID,
        cell_id=CELL_ID,
        allocation_ids={row["allocation_id"] for row in schedule["allocations"]},
        allocation_attempts=rows,
    )


def accepted_fixture(shared: Path, corpus: Path) -> Path:
    rows = (
        (
            "non-incremental/QF_BV/fixture/a.smt2",
            "QF_BV",
            "(set-logic QF_BV)\n(set-info :status sat)\n(check-sat)\n",
        ),
        (
            "non-incremental/QF_UF/fixture/b.smt2",
            "QF_UF",
            "(set-logic QF_UF)\n(set-info :status unsat)\n(check-sat)\n",
        ),
    )
    staging = shared / "accepted-staging"
    staging.mkdir()
    selected = staging / "official-selected.txt"
    selected.write_text("".join(f"{row[0]}\n" for row in rows), encoding="utf-8")
    ledger = staging / "selected-files.jsonl"
    ledger_bytes = bytearray()
    for benchmark_id, logic, content in rows:
        benchmark = corpus / benchmark_id
        benchmark.parent.mkdir(parents=True, exist_ok=True)
        benchmark.write_text(content, encoding="utf-8")
        ledger_bytes.extend(
            canonical_bytes(
                {
                    "archive": f"{logic}.tar.zst",
                    "benchmark_id": benchmark_id,
                    "bytes": benchmark.stat().st_size,
                    "logic": logic,
                    "sha256": sha256_file(benchmark),
                }
            )
        )
    ledger.write_bytes(bytes(ledger_bytes))
    completion = {
        "artifacts": {
            "official-selected.txt": sha256_file(selected),
            "selected-files.jsonl": sha256_file(ledger),
        },
        "authority_sha256": "a" * 64,
        "metadata_rows": len(rows),
        "payload_sha256": "",
        "schema": "axeyum-smtcomp-official-selection-v1",
        "selected_files": len(rows),
        "selection_observed": True,
        "status": "complete",
    }
    completion["payload_sha256"] = digest(
        {key: value for key, value in completion.items() if key != "payload_sha256"}
    )
    complete = staging / "complete.json"
    complete.write_bytes(canonical_bytes(completion))
    accepted = shared / f"accepted-{sha256_file(complete)}"
    staging.rename(accepted)
    return accepted


def readiness_repository(
    root: Path, required: tuple[str, ...] = ("a.txt", "b.txt")
) -> tuple[str, ...]:
    subprocess.run(["git", "init", "-b", "main"], cwd=root, check=True, capture_output=True)
    subprocess.run(
        ["git", "config", "user.email", "fixture@example.invalid"],
        cwd=root,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Fixture"], cwd=root, check=True
    )
    for path in required:
        target = root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(f"{path}\n", encoding="utf-8")
    subprocess.run(["git", "add", *required], cwd=root, check=True)
    subprocess.run(
        ["git", "commit", "-m", "fixture"], cwd=root, check=True, capture_output=True
    )
    subprocess.run(
        ["git", "update-ref", "refs/remotes/origin/main", "HEAD"],
        cwd=root,
        check=True,
    )
    return required


def incident_sentinel_fixture(
    *, attempt: Path, binaries: dict[str, Path], started_at_ns: int
) -> list[dict]:
    inputs = attempt / "inputs" / "sentinels"
    outputs = attempt / "sentinels" / "outputs"
    inputs.mkdir(parents=True)
    outputs.mkdir(parents=True)
    sentinel_paths = {}
    records = []
    for index, (sentinel_id, kind, solver_id) in enumerate(SENTINEL_ROWS):
        sentinel_path = sentinel_paths.get(sentinel_id)
        if sentinel_path is None:
            sentinel_path = inputs / f"{sentinel_id}.smt2"
            sentinel_path.write_text(f"; fixture {kind}\n(check-sat)\n", encoding="utf-8")
            sentinel_paths[sentinel_id] = sentinel_path
        status = "unsat" if kind != "qf_auflia" else (
            "unknown" if solver_id == "axeyum" else "sat"
        )
        stdout_path = outputs / f"{sentinel_id}-{solver_id}.stdout"
        stderr_path = outputs / f"{sentinel_id}-{solver_id}.stderr"
        stdout_path.write_text(f"{status}\n", encoding="ascii")
        stderr_path.write_bytes(b"")
        command = [str(binaries[solver_id]), str(sentinel_path)]
        if solver_id == "axeyum":
            command.extend(["--timeout-ms", "19000"])
        observed_at = started_at_ns + index * 10
        records.append(
            seal_sentinel(
                {
                    "schema": SENTINEL_SCHEMA,
                    "sentinel_id": sentinel_id,
                    "sentinel_kind": kind,
                    "sentinel_path": str(sentinel_path),
                    "sentinel_sha256": sha256_file(sentinel_path),
                    "solver_id": solver_id,
                    "solver_binary_sha256": sha256_file(binaries[solver_id]),
                    "command_sha256": digest(command),
                    "environment_sha256": digest(SOLVER_ENVIRONMENT),
                    "observed_status": status,
                    "termination_class": "completed",
                    "exit_code": 0,
                    "signal": None,
                    "resource_limit_kind": None,
                    "started_at_ns": observed_at,
                    "ended_at_ns": observed_at + 1,
                    "wall_time_ns": 1,
                    "runner_elapsed_ns": 1,
                    "stdout_path": str(stdout_path),
                    "stdout_sha256": sha256_file(stdout_path),
                    "stdout_bytes": stdout_path.stat().st_size,
                    "stderr_path": str(stderr_path),
                    "stderr_sha256": sha256_file(stderr_path),
                    "stderr_bytes": stderr_path.stat().st_size,
                }
            )
        )
    return records


class FullPopulationContractTests(unittest.TestCase):
    @staticmethod
    def sensors_json(temperature: object) -> bytes:
        return json.dumps(
            {"k10temp-pci-00c3": {"Tctl": {"temp1_input": temperature}}}
        ).encode("utf-8")

    def thermal_observations(
        self,
        schedule: dict,
        *,
        wave_index: int,
        temperatures: tuple[object, object, object],
        attempt_ids: tuple[str | None, str | None, str | None] = (None, None, None),
    ) -> list[dict]:
        wave = schedule["waves"][wave_index]
        return [
            build_thermal_observation(
                sensors_json=self.sensors_json(temperature),
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
                wave_index=wave_index,
                allocation_id=allocation_id,
                attempt_id=attempt_id,
                host_id=host_id,
                observed_at_ns=1000 + index,
            )
            for index, (host_id, allocation_id, attempt_id, temperature) in enumerate(
                zip(
                    wave["host_ids"],
                    wave["allocation_ids"],
                    attempt_ids,
                    temperatures,
                    strict=True,
                )
            )
        ]

    @staticmethod
    def wave_terminals(schedule: dict, wave_index: int) -> list[dict]:
        return [
            {
                "allocation_id": allocation_id,
                "attempt_id": f"attempt-{wave_index:02d}-{index}",
                "status": "completed",
                "terminal_record_sha256": f"{wave_index * 3 + index:064x}",
            }
            for index, allocation_id in enumerate(
                schedule["waves"][wave_index]["allocation_ids"]
            )
        ]

    def checkpoint(self, schedule: dict, wave_index: int) -> dict:
        return build_wave_checkpoint(
            schedule=schedule,
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
            wave_index=wave_index,
            allocation_terminals=self.wave_terminals(schedule, wave_index),
            cumulative_records=cumulative_benchmark_count(schedule, wave_index),
        )

    def test_population_is_identical_for_all_three_cells(self) -> None:
        contract = validate_population_contract(build_population_contract())
        self.assertEqual(contract["population_count"], POPULATION_COUNT)
        self.assertEqual(
            [cell["solver_id"] for cell in contract["cells"]], list(SOLVER_IDS)
        )
        identities = {
            (
                cell["population_count"],
                cell["full_list_sha256"],
                cell["full_manifest_sha256"],
            )
            for cell in contract["cells"]
        }
        self.assertEqual(len(identities), 1)

    def test_population_mutations_reject_even_when_resealed(self) -> None:
        for label, mutate in (
            ("count", lambda row: row.__setitem__("population_count", 45_904)),
            ("list", lambda row: row.__setitem__("full_list_sha256", "0" * 64)),
            (
                "manifest",
                lambda row: row["cells"][2].__setitem__(
                    "full_manifest_sha256", "1" * 64
                ),
            ),
            ("order", lambda row: row["cells"].reverse()),
            ("subset", lambda row: row["cells"].pop()),
        ):
            with self.subTest(label=label):
                mutated = build_population_contract()
                mutate(mutated)
                with self.assertRaises(ContractError):
                    validate_population_contract(reseal(mutated))

    def test_schedule_partitions_all_shards_into_sixteen_host_distinct_waves(self) -> None:
        schedule = validate_schedule(build_schedule(ENFORCEMENT_ID))
        allocations = schedule["allocations"]
        initial = allocations[:INITIAL_ALLOCATION_COUNT]
        retries = allocations[INITIAL_ALLOCATION_COUNT:]
        self.assertEqual(len(initial), INITIAL_ALLOCATION_COUNT)
        self.assertEqual(len(retries), RETRY_ALLOCATION_COUNT)
        self.assertEqual(len(schedule["waves"]), WAVE_COUNT)
        self.assertEqual(
            sorted(shard for row in initial for shard in row["shard_ids"]),
            list(range(SHARD_COUNT)),
        )
        self.assertEqual(
            sum(shard_benchmark_count(shard) for shard in range(SHARD_COUNT)),
            POPULATION_COUNT,
        )
        for wave_index, wave in enumerate(schedule["waves"]):
            self.assertEqual(wave["wave_index"], wave_index)
            self.assertEqual(wave["host_ids"], list(HOST_IDS))
            self.assertEqual(len(wave["allocation_ids"]), 3)
            self.assertEqual(len(wave["shard_ids"]), 6)
            self.assertEqual(
                wave["benchmark_count"],
                sum(shard_benchmark_count(shard) for shard in wave["shard_ids"]),
            )

    def test_every_shard_has_one_different_host_retry(self) -> None:
        allocations = build_schedule(ENFORCEMENT_ID)["allocations"]
        initial = {
            row["allocation_id"]: row
            for row in allocations
            if row["generation"] == 0
        }
        retries = [row for row in allocations if row["generation"] == 1]
        self.assertEqual(
            sorted(row["shard_ids"][0] for row in retries), list(range(SHARD_COUNT))
        )
        for retry in retries:
            owner = initial[retry["recovers_allocation_id"]]
            self.assertIn(retry["shard_ids"][0], owner["shard_ids"])
            self.assertNotEqual(retry["host_id"], owner["host_id"])

    def test_schedule_is_accepted_by_generic_multi_host_partition_gate(self) -> None:
        filesystem_id = "f" * 64
        environment_id = "d" * 64
        registrations = [
            reseal(
                {
                    "schema": REGISTRATION_SCHEMA,
                    "host_id": host_id,
                    "ssh_target": host_id,
                    "hostname": f"server-{host_id}",
                    "kernel_release": "fixture-kernel",
                    "machine": "x86_64",
                    "python_version": "3.fixture",
                    "python_executable_sha256": "1" * 64,
                    "toolchain_identity_sha256": "2" * 64,
                    "cgroup_controllers": ["cpu", "io", "memory", "pids"],
                    "user_systemd_transient": True,
                    "shared_filesystem_class_sha256": filesystem_id,
                    "environment_class_sha256": environment_id,
                }
            )
            for host_id in HOST_IDS
        ]
        run = {
            "identity_sha256": "a" * 64,
            "identity": {"shard_count": SHARD_COUNT},
            "resource_enforcement": {
                "kind": MULTI_HOST_KIND,
                "enforcement_id": ENFORCEMENT_ID,
            },
        }
        plan = seal_as(
            {
                "schema": PLAN_SCHEMA,
                "run_identity_sha256": run["identity_sha256"],
                "transport": TRANSPORT,
                "shared_root": "/fixture/shared",
                "shared_filesystem_class_sha256": filesystem_id,
                "environment_class_sha256": environment_id,
                "host_registrations": registrations,
                "allocations": build_schedule(ENFORCEMENT_ID)["allocations"],
                "fault_injection": {"kind": "none"},
            },
            "plan_sha256",
        )
        validate_plan(plan, run, inspect_shared_root=False)

    def test_schedule_resource_and_topology_mutations_reject(self) -> None:
        for label, mutate in (
            (
                "workers",
                lambda row: row["resources"].__setitem__("workers_per_allocation", 3),
            ),
            (
                "memory",
                lambda row: row["resources"].__setitem__(
                    "aggregate_memory_bytes", 8 * 1024**3
                ),
            ),
            (
                "same-host retry",
                lambda row: row["allocations"][INITIAL_ALLOCATION_COUNT].__setitem__(
                    "host_id", "s5"
                ),
            ),
            (
                "wave order",
                lambda row: row["waves"][0]["allocation_ids"].reverse(),
            ),
            ("missing retry", lambda row: row["allocations"].pop()),
        ):
            with self.subTest(label=label):
                mutated = build_schedule(ENFORCEMENT_ID)
                mutate(mutated)
                with self.assertRaises(ContractError):
                    validate_schedule(reseal(mutated))

    def test_bad_enforcement_identity_rejects(self) -> None:
        with self.assertRaises(ContractError):
            build_schedule("not-a-sha")

    def test_thermal_observation_requires_exact_sensor_and_numeric_value(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        observation = self.thermal_observations(
            schedule, wave_index=0, temperatures=(39.75, 40, 40.125)
        )[0]
        self.assertEqual(observation["temperature_millicelsius"], 39_750)
        self.assertEqual(observation["sensor_label"], "Tctl")
        self.assertEqual(
            bytes.fromhex(observation["sensors_json_hex"]), self.sensors_json(39.75)
        )

        for label, mutate in (
            (
                "claimed temperature",
                lambda row: row.__setitem__("temperature_millicelsius", 39_751),
            ),
            ("raw bytes", lambda row: row.__setitem__("sensors_json_hex", "00")),
            ("raw digest", lambda row: row.__setitem__("sensors_json_sha256", "0" * 64)),
            ("raw length", lambda row: row.__setitem__("sensors_json_bytes", 1)),
        ):
            with self.subTest(label=label):
                mutated = copy.deepcopy(observation)
                mutate(mutated)
                with self.assertRaises(ContractError):
                    validate_thermal_observation(reseal(mutated))

        malformed = (
            b"{}",
            self.sensors_json("90.0"),
            self.sensors_json(True),
            self.sensors_json(40.0001),
            b'{"k10temp-pci-00c3":{"Tctl":{"temp1_input":40,'
            b'"temp1_input":41}}}',
            b'{"k10temp-pci-00c3":{"Tctl":{"temp1_input":NaN}}}',
        )
        wave = schedule["waves"][0]
        for index, raw in enumerate(malformed):
            with self.subTest(index=index), self.assertRaises(ContractError):
                build_thermal_observation(
                    sensors_json=raw,
                    plan_sha256=PLAN_ID,
                    run_identity_sha256=RUN_ID,
                    cell_id=CELL_ID,
                    wave_index=0,
                    allocation_id=wave["allocation_ids"][0],
                    attempt_id=None,
                    host_id="s5",
                    observed_at_ns=1,
                )

    def test_thermal_threshold_and_cooldown_hysteresis_gate_launch(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)

        def decide(temperatures: tuple[object, object, object], cooldown: bool) -> dict:
            return scheduler_decision(
                schedule=schedule,
                checkpoints=[],
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
                allocation_scheduler_state=scheduler_state(schedule),
                pause_requested=False,
                cooldown_required=cooldown,
                thermal_observations=self.thermal_observations(
                    schedule, wave_index=0, temperatures=temperatures
                ),
                decided_at_ns=2000,
            )

        self.assertEqual(decide((89.999, 70, 70), False)["status"], "launch")
        self.assertEqual(
            decide((90, 70, 70), False)["status"], "thermal-stop-required"
        )
        self.assertEqual(decide((79.999, 70, 70), True)["status"], "launch")
        self.assertEqual(decide((80, 70, 70), True)["status"], "thermal-cooldown")

    def test_thermal_launch_requires_exact_three_host_wave_identity(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        observations = self.thermal_observations(
            schedule, wave_index=0, temperatures=(40, 40, 40)
        )
        for label, mutate in (
            ("missing", lambda rows: rows.pop()),
            ("duplicate", lambda rows: rows.__setitem__(2, rows[0])),
            (
                "active attempt",
                lambda rows: rows[0].__setitem__("attempt_id", "already-running"),
            ),
            (
                "wrong allocation",
                lambda rows: rows[0].__setitem__("allocation_id", "full-initial-03"),
            ),
        ):
            with self.subTest(label=label):
                mutated = copy.deepcopy(observations)
                mutate(mutated)
                if label not in {"missing", "duplicate"}:
                    mutated[0] = reseal(mutated[0])
                with self.assertRaises(ContractError):
                    scheduler_decision(
                        schedule=schedule,
                        checkpoints=[],
                        plan_sha256=PLAN_ID,
                        run_identity_sha256=RUN_ID,
                        cell_id=CELL_ID,
                        allocation_scheduler_state=scheduler_state(schedule),
                        pause_requested=False,
                        cooldown_required=False,
                        thermal_observations=mutated,
                        decided_at_ns=2000,
                    )

        with self.assertRaises(ContractError):
            scheduler_decision(
                schedule=schedule,
                checkpoints=[],
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
                allocation_scheduler_state=scheduler_state(schedule),
                pause_requested=False,
                cooldown_required=False,
                thermal_observations=observations,
                decided_at_ns=60_000_001_001,
            )

    def test_wave_checkpoint_is_deterministic_and_drives_restart_skip(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        checkpoint = self.checkpoint(schedule, 0)
        self.assertEqual(checkpoint, self.checkpoint(schedule, 0))
        decision = scheduler_decision(
            schedule=schedule,
            checkpoints=[checkpoint],
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
            allocation_scheduler_state=scheduler_state(
                schedule,
                completed_allocation_ids=sorted(
                    {
                        row["allocation_id"]
                        for row in checkpoint["shard_completions"]
                    }
                ),
            ),
            pause_requested=False,
            cooldown_required=False,
            thermal_observations=self.thermal_observations(
                schedule, wave_index=1, temperatures=(40, 40, 40)
            ),
            decided_at_ns=2000,
        )
        self.assertEqual(decision["status"], "launch")
        self.assertEqual(decision["next_wave_index"], 1)
        self.assertEqual(
            decision["allocation_ids"], schedule["waves"][1]["allocation_ids"]
        )

    def test_checkpoint_mutations_and_noncontiguous_chain_reject(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        checkpoint = self.checkpoint(schedule, 0)
        for label, mutate in (
            (
                "terminal",
                lambda row: row["shard_completions"][0].__setitem__(
                    "status", "failed"
                ),
            ),
            (
                "count",
                lambda row: row.__setitem__("cumulative_benchmark_count", 1),
            ),
            ("next", lambda row: row.__setitem__("next_wave_index", 2)),
        ):
            with self.subTest(label=label):
                mutated = copy.deepcopy(checkpoint)
                mutate(mutated)
                with self.assertRaises(ContractError):
                    validate_wave_checkpoint(
                        reseal(mutated),
                        schedule=schedule,
                        plan_sha256=PLAN_ID,
                        run_identity_sha256=RUN_ID,
                        cell_id=CELL_ID,
                    )
        with self.assertRaises(ContractError):
            scheduler_decision(
                schedule=schedule,
                checkpoints=[self.checkpoint(schedule, 1)],
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
                allocation_scheduler_state=scheduler_state(schedule),
                pause_requested=False,
                cooldown_required=False,
                thermal_observations=[],
                decided_at_ns=2000,
            )

    def test_recovered_wave_checkpoint_requires_each_exact_shard_retry(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        terminals = self.wave_terminals(schedule, 0)[1:]
        terminals.extend(
            [
                {
                    "allocation_id": f"full-retry-{shard_id:02d}",
                    "attempt_id": f"retry-attempt-{shard_id:02d}",
                    "status": "completed",
                    "terminal_record_sha256": f"{100 + shard_id:064x}",
                }
                for shard_id in (0, 1)
            ]
        )
        checkpoint = build_wave_checkpoint(
            schedule=schedule,
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
            wave_index=0,
            allocation_terminals=terminals,
            cumulative_records=cumulative_benchmark_count(schedule, 0),
        )
        self.assertEqual(
            [row["allocation_id"] for row in checkpoint["shard_completions"][:2]],
            ["full-retry-00", "full-retry-01"],
        )
        self.assertEqual(
            [row["allocation_id"] for row in checkpoint["shard_completions"][2:4]],
            ["full-initial-01", "full-initial-01"],
        )

        missing = terminals[:-1]
        with self.assertRaisesRegex(ContractError, "every exact wave shard"):
            build_wave_checkpoint(
                schedule=schedule,
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
                wave_index=0,
                allocation_terminals=missing,
                cumulative_records=cumulative_benchmark_count(schedule, 0),
            )
        mutated = copy.deepcopy(checkpoint)
        mutated["shard_completions"][0]["allocation_id"] = "full-retry-02"
        with self.assertRaisesRegex(ContractError, "not valid for wave shard"):
            validate_wave_checkpoint(
                reseal(mutated),
                schedule=schedule,
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
            )

    def test_scheduler_never_launches_around_unclosed_failure_loss_or_pause(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        cases = (
            ("blocked-unclosed", ["attempt-open"], [], [], False),
            ("blocked-failure", [], ["full-initial-00"], [], False),
            ("blocked-failure", [], [], ["full-initial-01"], False),
            ("paused", [], [], [], True),
        )
        for expected, opens, failed, lost, pause in cases:
            with self.subTest(expected=expected, failed=failed, lost=lost):
                decision = scheduler_decision(
                    schedule=schedule,
                    checkpoints=[],
                    plan_sha256=PLAN_ID,
                    run_identity_sha256=RUN_ID,
                    cell_id=CELL_ID,
                    allocation_scheduler_state=scheduler_state(
                        schedule,
                        open_attempt_ids=opens,
                        failed_allocation_ids=failed,
                        lost_allocation_ids=lost,
                    ),
                    pause_requested=pause,
                    cooldown_required=False,
                    thermal_observations=[],
                    decided_at_ns=2000,
                )
                self.assertEqual(decision["status"], expected)
                self.assertEqual(decision["allocation_ids"], [])

    def test_scheduler_recovers_exact_completed_wave_without_relaunch(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        completed = schedule["waves"][0]["allocation_ids"]
        state = scheduler_state(
            schedule,
            completed_allocation_ids=completed,
        )
        recover = scheduler_decision(
            schedule=schedule,
            checkpoints=[],
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
            allocation_scheduler_state=state,
            pause_requested=False,
            cooldown_required=False,
            thermal_observations=[],
            decided_at_ns=2000,
        )
        self.assertEqual(recover["status"], "recover-checkpoint")
        self.assertEqual(
            recover["uncheckpointed_completed_allocation_ids"], completed
        )
        self.assertEqual(recover["allocation_ids"], [])
        checkpoint = validate_wave_checkpoint(
            recover["recovery_checkpoint"],
            schedule=schedule,
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
        )
        self.assertEqual(checkpoint["wave_index"], 0)
        self.assertEqual(
            sorted(
                {
                    row["allocation_id"]
                    for row in checkpoint["shard_completions"]
                }
            ),
            completed,
        )

        partial = scheduler_decision(
            schedule=schedule,
            checkpoints=[],
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
            allocation_scheduler_state=scheduler_state(
                schedule,
                completed_allocation_ids=completed[:1],
            ),
            pause_requested=False,
            cooldown_required=False,
            thermal_observations=[],
            decided_at_ns=2000,
        )
        self.assertEqual(partial["status"], "blocked-uncheckpointed")
        self.assertIsNone(partial["recovery_checkpoint"])

        resumed = scheduler_decision(
            schedule=schedule,
            checkpoints=[checkpoint],
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
            allocation_scheduler_state=state,
            pause_requested=False,
            cooldown_required=False,
            thermal_observations=self.thermal_observations(
                schedule, wave_index=1, temperatures=(40, 40, 40)
            ),
            decided_at_ns=2000,
        )
        self.assertEqual(resumed["status"], "launch")
        self.assertEqual(resumed["next_wave_index"], 1)
        self.assertIsNone(resumed["recovery_checkpoint"])

        with self.assertRaisesRegex(ContractError, "without a completed terminal"):
            scheduler_decision(
                schedule=schedule,
                checkpoints=[checkpoint],
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
                allocation_scheduler_state=scheduler_state(schedule),
                pause_requested=False,
                cooldown_required=False,
                thermal_observations=[],
                decided_at_ns=2000,
            )

    def test_scheduler_recovery_closes_failed_initial_with_exact_retries(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        allocations = {
            row["allocation_id"]: row for row in schedule["allocations"]
        }
        failed = schedule["waves"][0]["allocation_ids"][0]
        unaffected = schedule["waves"][0]["allocation_ids"][1:]
        retries = sorted(
            row["allocation_id"]
            for row in schedule["allocations"]
            if row["generation"] == 1
            and row["recovers_allocation_id"] == failed
        )
        self.assertEqual(
            {shard for retry in retries for shard in allocations[retry]["shard_ids"]},
            set(allocations[failed]["shard_ids"]),
        )
        state = scheduler_state(
            schedule,
            completed_allocation_ids=[*unaffected, *retries],
            failed_allocation_ids=[failed],
        )
        recovery = scheduler_decision(
            schedule=schedule,
            checkpoints=[],
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
            allocation_scheduler_state=state,
            pause_requested=False,
            cooldown_required=False,
            thermal_observations=[],
            decided_at_ns=2000,
        )
        self.assertEqual(recovery["status"], "recover-checkpoint")
        self.assertEqual(recovery["failed_allocation_ids"], [failed])
        checkpoint = recovery["recovery_checkpoint"]
        retried_completions = {
            row["allocation_id"]
            for row in checkpoint["shard_completions"]
            if row["shard_id"] in allocations[failed]["shard_ids"]
        }
        self.assertEqual(retried_completions, set(retries))

        resumed = scheduler_decision(
            schedule=schedule,
            checkpoints=[checkpoint],
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
            allocation_scheduler_state=state,
            pause_requested=False,
            cooldown_required=False,
            thermal_observations=self.thermal_observations(
                schedule, wave_index=1, temperatures=(40, 40, 40)
            ),
            decided_at_ns=2000,
        )
        self.assertEqual(resumed["status"], "launch")
        self.assertEqual(resumed["failed_allocation_ids"], [])

    def test_all_sixteen_checkpoints_close_the_cell_without_thermal_probe(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        checkpoints = [self.checkpoint(schedule, index) for index in range(WAVE_COUNT)]
        completed = sorted(
            {
                row["allocation_id"]
                for checkpoint in checkpoints
                for row in checkpoint["shard_completions"]
            }
        )
        decision = scheduler_decision(
            schedule=schedule,
            checkpoints=checkpoints,
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
            allocation_scheduler_state=scheduler_state(
                schedule,
                completed_allocation_ids=completed,
            ),
            pause_requested=False,
            cooldown_required=False,
            thermal_observations=[],
            decided_at_ns=2000,
        )
        self.assertEqual(decision["status"], "complete")
        self.assertIsNone(decision["next_wave_index"])
        self.assertEqual(checkpoints[-1]["cumulative_benchmark_count"], POPULATION_COUNT)

    def test_thermal_stop_binds_active_attempt_and_exact_systemd_unit(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        observation = self.thermal_observations(
            schedule,
            wave_index=0,
            temperatures=(90, 40, 40),
            attempt_ids=("active-attempt", None, None),
        )[0]
        record = build_thermal_stop(
            observation=observation,
            session_id="session-001",
            unit_prefix=UNIT_PREFIX,
            exit_code=0,
            post_stop_unit_state="inactive",
            stopped_at_ns=2000,
        )
        self.assertEqual(
            record["command"],
            [
                "systemctl",
                "--user",
                "stop",
                "axeyum-smtcomp-full-session-001.service",
            ],
        )
        for label, mutate in (
            ("blanket", lambda row: row.__setitem__("command", ["pkill", "solver"])),
            (
                "other unit",
                lambda row: row.__setitem__(
                    "remote_unit", "axeyum-smtcomp-full-other.service"
                ),
            ),
            ("failed stop", lambda row: row.__setitem__("exit_code", 1)),
            (
                "active state",
                lambda row: row.__setitem__("post_stop_unit_state", "active"),
            ),
        ):
            with self.subTest(label=label):
                mutated = copy.deepcopy(record)
                mutate(mutated)
                with self.assertRaises(ContractError):
                    validate_thermal_stop(
                        reseal(mutated),
                        observation=observation,
                        session_id="session-001",
                        unit_prefix=UNIT_PREFIX,
                    )

        cool = self.thermal_observations(
            schedule,
            wave_index=0,
            temperatures=(89.999, 40, 40),
            attempt_ids=("active-attempt", None, None),
        )[0]
        with self.assertRaises(ContractError):
            build_thermal_stop(
                observation=cool,
                session_id="session-001",
                unit_prefix=UNIT_PREFIX,
                exit_code=0,
                post_stop_unit_state="inactive",
                stopped_at_ns=2000,
            )

    def test_fixture_selection_materialization_rehashes_every_selected_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shared = root / "shared"
            corpus = shared / "corpus"
            output = shared / "output"
            output.mkdir(parents=True)
            accepted = accepted_fixture(shared, corpus)
            record = materialize_full_selection(
                accepted_root=accepted,
                corpus_root=corpus,
                output_dir=output,
                fixture_only=True,
            )
            self.assertEqual(record["population_count"], 2)
            self.assertFalse(record["launch_authorized"])
            self.assertEqual(
                validate_full_selection(record)["record_sha256"],
                record["record_sha256"],
            )
            benchmark = corpus / "non-incremental/QF_BV/fixture/a.smt2"
            benchmark.write_text("mutated\n", encoding="utf-8")
            with self.assertRaises(ContractError):
                validate_full_selection(record)

    def test_fixture_population_cannot_pass_the_live_preregistration_gate(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shared = root / "shared"
            corpus = shared / "corpus"
            output = shared / "output"
            output.mkdir(parents=True)
            accepted = accepted_fixture(shared, corpus)
            with self.assertRaisesRegex(ContractError, "differs from preregistration"):
                materialize_full_selection(
                    accepted_root=accepted,
                    corpus_root=corpus,
                    output_dir=output,
                    fixture_only=False,
                )

    def test_full_host_argv_freezes_multi_shard_workers_and_no_launch_side_effect(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            staged = root / "staged"
            staged.mkdir()
            solver = root / "solver"
            solver.write_bytes(b"fixture solver")
            paths = {}
            for name in (
                "files.txt",
                "run.json",
                "selection.json",
                "accepted",
                "corpus.json",
                "environment.json",
                "source-identity.json",
            ):
                path = root / name
                if name == "accepted":
                    path.mkdir()
                else:
                    path.write_bytes(b"fixture\n")
                paths[name] = path
            (staged / "compete.py").write_bytes(b"fixture\n")
            run_dir = root / "run"
            run_dir.mkdir()
            argv = full_host_argv(
                python_executable=Path(sys.executable),
                staged_source=staged,
                solver_id="axeyum",
                solver_binary=solver,
                shard_ids=[0, 1],
                session_id="full-axeyum-initial-00",
                file_list=paths["files.txt"],
                run_manifest=paths["run.json"],
                run_dir=run_dir,
                selection_manifest=paths["selection.json"],
                accepted_root=paths["accepted"],
                corpus_manifest=paths["corpus.json"],
                environment_manifest=paths["environment.json"],
                source_identity_manifest=paths["source-identity.json"],
                internal_timeout_ms=19_000,
            )
            self.assertEqual(argv[argv.index("--host-shards") + 1], "0,1")
            self.assertEqual(argv[argv.index("--internal-timeout-ms") + 1], "19000")
            self.assertNotIn("--allow-unadmitted-selection-fixture", argv)
            self.assertEqual(
                [
                    argv[index + 1]
                    for index, value in enumerate(argv)
                    if value == "--solver-env"
                ],
                ["AYU_THREADS=1", "OMP_NUM_THREADS=1", "RAYON_NUM_THREADS=1"],
            )
            with self.assertRaises(ContractError):
                full_host_argv(
                    python_executable=Path(sys.executable),
                    staged_source=staged,
                    solver_id="cvc5",
                    solver_binary=solver,
                    shard_ids=[1, 0],
                    session_id="bad",
                    file_list=paths["files.txt"],
                    run_manifest=paths["run.json"],
                    run_dir=run_dir,
                    selection_manifest=paths["selection.json"],
                    accepted_root=paths["accepted"],
                    corpus_manifest=paths["corpus.json"],
                    environment_manifest=paths["environment.json"],
                    source_identity_manifest=paths["source-identity.json"],
                )

    def test_fixture_composer_publishes_all_cell_manifests_without_attempts(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shared = root / "shared"
            corpus = shared / "corpus"
            attempt = shared / "attempt"
            selection_dir = attempt / "inputs"
            selection_dir.mkdir(parents=True)
            accepted = accepted_fixture(shared, corpus)
            selection = materialize_full_selection(
                accepted_root=accepted,
                corpus_root=corpus,
                output_dir=selection_dir,
                fixture_only=True,
            )
            corpus_manifest = selection_dir / "corpus.json"
            environment_manifest = selection_dir / "environment.json"
            corpus_manifest.write_bytes(canonical_bytes({"fixture": "corpus"}))
            filesystem = {
                "source": "fixture:/shared",
                "filesystem_type": "nfs4",
                "mount_point": str(shared),
                "options": ["hard", "local_lock=none", "vers=4.1"],
            }
            filesystem["class_sha256"] = digest(filesystem)
            filesystem_sha = filesystem["class_sha256"]
            observations = [
                reseal(
                    {
                        "schema": OBSERVATION_SCHEMA,
                        "hostname": f"server-{host_id}",
                        "kernel_release": "fixture-kernel",
                        "machine": "x86_64",
                        "python_version": "3.fixture",
                        "python_executable_sha256": sha256_file(
                            Path(sys.executable).resolve()
                        ),
                        "toolchain_identity_sha256": "2" * 64,
                        "cgroup_controllers": ["cpu", "io", "memory", "pids"],
                        "user_systemd_transient": True,
                        "shared_filesystem": filesystem,
                        "shared_filesystem_class_sha256": filesystem_sha,
                    }
                )
                for host_id in HOST_IDS
            ]
            environment = multi_host_module.environment_manifest(observations)
            environment_manifest.write_bytes(canonical_bytes(environment))
            environment_sha = sha256_file(environment_manifest)
            registrations = [
                host_registration(
                    host_id=host_id,
                    ssh_target=host_id,
                    observation=observation,
                    environment_sha256=environment_sha,
                )
                for host_id, observation in zip(HOST_IDS, observations, strict=True)
            ]
            fixture_root = root / "empty-fixtures"
            fixture_root.mkdir()
            staging_parent = attempt / "source-bundles"
            staging_parent.mkdir()
            bundle_root, source_identity = stage_execution_bundle(
                repository_root=ROOT,
                source_root=SMTCOMP,
                fixture_root=fixture_root,
                staging_parent=staging_parent,
            )
            staged_source = bundle_root / "scripts" / "smtcomp_repro"
            source_identity_path = bundle_root / "source-identity.json"
            binaries = []
            binary_root = attempt / "binaries"
            binary_root.mkdir()
            for solver_id in SOLVER_IDS:
                binary = binary_root / solver_id
                binary.write_bytes(f"{solver_id} fixture".encode("ascii"))
                binary.chmod(0o755)
                binaries.append(binary)
            cells = [
                FullSolverCell("axeyum", binaries[0], "fixture", 19_000),
                FullSolverCell("cvc5", binaries[1], "fixture"),
                FullSolverCell("bitwuzla", binaries[2], "fixture"),
            ]
            with mock.patch(
                "multi_host.shared_filesystem_observation",
                return_value={"class_sha256": filesystem_sha},
            ):
                composition = compose_full_cell_manifests(
                    repository_root=ROOT,
                    source_root=staged_source,
                    shared_root=shared,
                    attempt_root=attempt,
                    selection=selection,
                    corpus_manifest=corpus_manifest,
                    environment_manifest=environment_manifest,
                    source_identity_manifest=source_identity_path,
                    host_registrations=registrations,
                    solver_cells=cells,
                    fixture_only=True,
                )
            composed = composition["cells"]
            self.assertEqual([row["solver_id"] for row in composed], list(SOLVER_IDS))
            self.assertFalse(composition["launch_authorized"])
            self.assertEqual(
                {row["selection_record_sha256"] for row in composed},
                {selection["record_sha256"]},
            )
            for cell in composed:
                self.assertEqual(len(cell["commands"]), 144)
                run = read_canonical_json(Path(cell["run_manifest_path"]))
                self.assertEqual(run["identity"]["shard_count"], SHARD_COUNT)
                self.assertEqual(run["resource_enforcement"]["worker_slots"], 2)
                self.assertEqual(
                    run["resource_enforcement"]["aggregate_memory_bytes"],
                    16 * 1024**3,
                )
                run_root = attempt / "cells" / cell["solver_id"]
                self.assertFalse(any((run_root / "multi-host-attempts").iterdir()))
                self.assertFalse(any((run_root / "multi-host-terminals").iterdir()))
            first = read_canonical_json(
                Path(composed[0]["commands"][0]["path"])
            )
            retry = read_canonical_json(
                Path(composed[0]["commands"][48]["path"])
            )
            self.assertEqual(
                first["argv"][first["argv"].index("--host-shards") + 1], "0,1"
            )
            self.assertEqual(
                retry["argv"][retry["argv"].index("--host-shards") + 1], "0"
            )
            self.assertIn("--allow-unadmitted-selection-fixture", first["argv"])
            mutated = copy.deepcopy(composition)
            mutated["cells"][0]["commands"][0]["shard_ids"] = [1, 0]
            with self.assertRaises(ContractError):
                validate_full_cell_composition(
                    reseal(mutated),
                    selection=selection,
                    inspect_shared_root=False,
                )

            gates = [
                build_gate_observation(
                    repository_root=ROOT,
                    command=list(command),
                    exit_code=0,
                    stdout=b"fixture-only green\n",
                    stderr=b"",
                    started_at_ns=3000 + index * 10,
                    ended_at_ns=3001 + index * 10,
                )
                for index, command in enumerate(
                    (("just", "check"), ("./scripts/check-smtcomp-resume.sh",))
                )
            ]
            readiness = build_readiness(
                repository_root=ROOT,
                gate_observations=gates,
                required_paths=("scripts/smtcomp_repro/full_population.py",),
                fixture_only=True,
            )
            binaries_by_solver = {
                cell.solver_id: cell.binary for cell in cells
            }
            sentinel_records = incident_sentinel_fixture(
                attempt=attempt,
                binaries=binaries_by_solver,
                started_at_ns=5000,
            )
            preflight = build_full_preflight(
                attempt_root=attempt,
                environment_path=environment_manifest,
                composition=composition,
                solver_binaries=binaries_by_solver,
                host_observations=observations,
                sentinel_records=sentinel_records,
                started_at_ns=4900,
                ended_at_ns=5100,
                fixture_only=True,
            )
            reordered = copy.deepcopy(preflight)
            reordered["sentinel_records"][0], reordered["sentinel_records"][1] = (
                reordered["sentinel_records"][1],
                reordered["sentinel_records"][0],
            )
            with self.assertRaisesRegex(ContractError, "order/identity"):
                validate_full_preflight(
                    reseal(reordered),
                    attempt_root=attempt,
                    composition=composition,
                    solver_binaries=binaries_by_solver,
                    prepared_at_ns=5200,
                )
            missing = copy.deepcopy(preflight)
            missing["sentinel_records"].pop()
            with self.assertRaisesRegex(ContractError, "row inventory"):
                validate_full_preflight(
                    reseal(missing),
                    attempt_root=attempt,
                    composition=composition,
                    solver_binaries=binaries_by_solver,
                    prepared_at_ns=5200,
                )
            duplicate = copy.deepcopy(preflight)
            duplicate["sentinel_records"][-1] = copy.deepcopy(
                duplicate["sentinel_records"][0]
            )
            with self.assertRaisesRegex(ContractError, "order/identity"):
                validate_full_preflight(
                    reseal(duplicate),
                    attempt_root=attempt,
                    composition=composition,
                    solver_binaries=binaries_by_solver,
                    prepared_at_ns=5200,
                )
            host_drift = copy.deepcopy(preflight)
            host_drift["host_observations"][0]["hostname"] = "other-host"
            host_drift["host_observations"][0] = reseal(
                host_drift["host_observations"][0]
            )
            with self.assertRaises(ContractError):
                validate_full_preflight(
                    reseal(host_drift),
                    attempt_root=attempt,
                    composition=composition,
                    solver_binaries=binaries_by_solver,
                    prepared_at_ns=5200,
                )
            unsafe = copy.deepcopy(preflight)
            unsafe_stdout = Path(unsafe["sentinel_records"][0]["stdout_path"])
            unsafe_stdout.write_bytes(b"sat\n")
            unsafe["sentinel_records"][0]["observed_status"] = "sat"
            unsafe["sentinel_records"][0]["stdout_sha256"] = sha256_file(
                unsafe_stdout
            )
            unsafe["sentinel_records"][0]["stdout_bytes"] = (
                unsafe_stdout.stat().st_size
            )
            unsafe["sentinel_records"][0] = seal_sentinel(
                unsafe["sentinel_records"][0]
            )
            with self.assertRaisesRegex(ContractError, "outcome is unsafe"):
                validate_full_preflight(
                    reseal(unsafe),
                    attempt_root=attempt,
                    composition=composition,
                    solver_binaries=binaries_by_solver,
                    prepared_at_ns=5200,
                )
            unsafe_stdout.write_bytes(b"unsat\n")
            with self.assertRaisesRegex(ContractError, "outside capture window"):
                validate_full_preflight(
                    preflight,
                    attempt_root=attempt,
                    composition=composition,
                    solver_binaries=binaries_by_solver,
                    prepared_at_ns=4900 + PREFLIGHT_MAX_AGE_NS + 1,
                )
            original_install = full_prepare_module.atomic_install_json
            with mock.patch.object(
                full_prepare_module,
                "atomic_install_json",
                wraps=original_install,
            ) as install:
                completion = publish_full_preparation_candidate(
                    repository_root=ROOT,
                    source_root=staged_source,
                    source_identity_manifest=source_identity_path,
                    attempt_root=attempt,
                    selection=selection,
                    composition=composition,
                    readiness=readiness,
                    preflight=preflight,
                    solver_cells=cells,
                    prepared_at_ns=5200,
                )
            self.assertEqual(install.call_args_list[-1].args[1], "complete.json")
            self.assertEqual(completion["status"], "prepared-no-launch")
            self.assertFalse(completion["launch_authorized"])
            self.assertTrue((attempt / "complete.json").is_file())
            self.assertEqual(
                validate_full_preparation(
                    attempt,
                    repository_root=ROOT,
                    inspect_shared_root=False,
                )["record_sha256"],
                completion["record_sha256"],
            )
            acceptance = build_full_preparation_acceptance(
                execution_source_commit=readiness["head_commit"],
                preparation_record_sha256=completion["record_sha256"],
                selection_record_sha256=selection["record_sha256"],
                fixture_only=True,
            )
            admission = build_full_cell_admission(
                attempt,
                repository_root=ROOT,
                solver_id="axeyum",
                expected_logic_counts={"QF_BV": 1, "QF_UF": 1},
                prior_result_roots={},
                acceptance=acceptance,
                inspect_shared_root=False,
                admitted_at_ns=5300,
            )
            self.assertEqual(
                validate_full_cell_admission(
                    admission,
                    preparation_root=attempt,
                    repository_root=ROOT,
                    expected_logic_counts={"QF_BV": 1, "QF_UF": 1},
                    prior_result_roots={},
                    acceptance=acceptance,
                    inspect_shared_root=False,
                ),
                admission,
            )
            drifted_acceptance = copy.deepcopy(acceptance)
            drifted_acceptance["preparation_record_sha256"] = "0" * 64
            with self.assertRaisesRegex(ContractError, "acceptance/preparation"):
                validate_full_cell_admission(
                    admission,
                    preparation_root=attempt,
                    repository_root=ROOT,
                    expected_logic_counts={"QF_BV": 1, "QF_UF": 1},
                    prior_result_roots={},
                    acceptance=reseal(drifted_acceptance),
                    inspect_shared_root=False,
                )
            drifted_admission = copy.deepcopy(admission)
            drifted_admission["plan_sha256"] = "0" * 64
            with self.assertRaisesRegex(ContractError, "admission replay drift"):
                validate_full_cell_admission(
                    reseal(drifted_admission),
                    preparation_root=attempt,
                    repository_root=ROOT,
                    expected_logic_counts={"QF_BV": 1, "QF_UF": 1},
                    prior_result_roots={},
                    acceptance=acceptance,
                    inspect_shared_root=False,
                )
            with self.assertRaisesRegex(ContractError, "prior-result order"):
                build_full_cell_admission(
                    attempt,
                    repository_root=ROOT,
                    solver_id="cvc5",
                    expected_logic_counts={"QF_BV": 1, "QF_UF": 1},
                    prior_result_roots={},
                    acceptance=acceptance,
                    inspect_shared_root=False,
                    admitted_at_ns=5300,
                )
            evidence = attempt / "cells" / "axeyum" / "records" / "unexpected"
            evidence.write_bytes(b"must reject pre-existing execution evidence\n")
            with self.assertRaisesRegex(ContractError, "execution evidence"):
                validate_full_preparation(
                    attempt,
                    repository_root=ROOT,
                    inspect_shared_root=False,
                )
            self.assertEqual(
                validate_full_preparation(
                    attempt,
                    repository_root=ROOT,
                    inspect_shared_root=False,
                    allowed_execution_solver_ids=("axeyum",),
                )["record_sha256"],
                completion["record_sha256"],
            )
            self.assertEqual(
                validate_full_cell_admission(
                    admission,
                    preparation_root=attempt,
                    repository_root=ROOT,
                    expected_logic_counts={"QF_BV": 1, "QF_UF": 1},
                    prior_result_roots={},
                    acceptance=acceptance,
                    inspect_shared_root=False,
                ),
                admission,
            )
            with self.assertRaisesRegex(ContractError, "solver prefix"):
                validate_full_preparation(
                    attempt,
                    repository_root=ROOT,
                    inspect_shared_root=False,
                    allowed_execution_solver_ids=("cvc5",),
                )
            later_cell_evidence = (
                attempt / "cells" / "cvc5" / "records" / "unexpected"
            )
            later_cell_evidence.write_bytes(b"later cell must remain empty\n")
            with self.assertRaisesRegex(ContractError, "execution evidence"):
                validate_full_preparation(
                    attempt,
                    repository_root=ROOT,
                    inspect_shared_root=False,
                    allowed_execution_solver_ids=("axeyum",),
                )
            later_cell_evidence.unlink()
            evidence.unlink()
            sentinel_stdout = Path(sentinel_records[0]["stdout_path"])
            sentinel_stdout.write_bytes(b"sat\n")
            with self.assertRaises(ContractError):
                validate_full_preparation(
                    attempt,
                    repository_root=ROOT,
                    inspect_shared_root=False,
                )
            sentinel_stdout.write_bytes(b"unsat\n")
            binaries[0].write_bytes(b"mutated solver")
            with self.assertRaises(ContractError):
                validate_full_preparation(
                    attempt,
                    repository_root=ROOT,
                    inspect_shared_root=False,
                )

    def test_remote_helper_thermal_stop_uses_only_exact_systemd_unit(self) -> None:
        unit = "axeyum-smtcomp-e3-full-axeyum-initial-00.service"
        active = mock.Mock(returncode=0, stdout="active\n")
        stopped = mock.Mock(returncode=0, stderr=b"")
        inactive = mock.Mock(returncode=3, stdout="inactive\n")
        with (
            mock.patch(
                "multi_host.subprocess.run", side_effect=[active, stopped, inactive]
            ) as run,
            mock.patch("multi_host.time.time_ns", return_value=1234),
        ):
            evidence = multi_host_module._stop_unit(unit)
        self.assertEqual(evidence["post_stop_unit_state"], "inactive")
        self.assertEqual(
            evidence["command"], ["systemctl", "--user", "stop", unit]
        )
        self.assertEqual(run.call_args_list[1].args[0], evidence["command"])
        self.assertNotIn("pkill", repr(run.call_args_list))
        self.assertNotIn("kill", repr(run.call_args_list))

        with mock.patch(
            "multi_host.subprocess.run",
            return_value=mock.Mock(returncode=3, stdout="inactive\n"),
        ):
            with self.assertRaises(ContractError):
                multi_host_module._stop_unit(unit)
        with self.assertRaises(ContractError):
            multi_host_module._stop_unit("unrelated.service")

    def test_remote_thermal_stop_rejects_noncanonical_or_mutated_evidence(self) -> None:
        unit = "axeyum-smtcomp-e3-full-axeyum-initial-00.service"
        valid = {
            "unit": unit,
            "command": ["systemctl", "--user", "stop", unit],
            "pre_stop_unit_state": "active",
            "exit_code": 0,
            "post_stop_unit_state": "inactive",
            "stopped_at_ns": 1234,
        }
        completed = mock.Mock(
            returncode=0,
            stdout=canonical_bytes(valid),
            stderr=b"",
        )
        with mock.patch("multi_host.subprocess.run", return_value=completed) as run:
            self.assertEqual(
                stop_remote_unit(
                    registration={"ssh_target": "s5"},
                    remote_helper_path=Path("/tmp/full-multi-host.py"),
                    unit=unit,
                ),
                valid,
            )
        self.assertIn("stop-unit", run.call_args.args[0])
        self.assertNotIn("pkill", run.call_args.args[0])

        mutated = {**valid, "command": ["pkill", "solver"]}
        completed.stdout = canonical_bytes(mutated)
        with mock.patch("multi_host.subprocess.run", return_value=completed):
            with self.assertRaises(ContractError):
                stop_remote_unit(
                    registration={"ssh_target": "s5"},
                    remote_helper_path=Path("/tmp/full-multi-host.py"),
                    unit=unit,
                )

    def test_supervised_wave_closes_checkpoint_and_honors_boundary_pause(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        prewave = self.thermal_observations(
            schedule, wave_index=0, temperatures=(40, 40, 40)
        )

        def launch(allocation: dict) -> WaveHandle:
            session = f"session-{allocation['allocation_id']}"
            return WaveHandle(
                allocation_id=allocation["allocation_id"],
                host_id=allocation["host_id"],
                attempt_id=f"attempt-{allocation['allocation_id']}",
                session_id=session,
                remote_unit=f"axeyum-smtcomp-e3-{session}.service",
            )

        def terminal(handle: WaveHandle) -> dict:
            return {
                "allocation_id": handle.allocation_id,
                "attempt_id": handle.attempt_id,
                "status": "completed",
                "terminal_record_sha256": "3" * 64,
            }

        for paused, expected in ((False, "wave-completed"), (True, "wave-completed-paused")):
            pause_calls = 0

            def pause() -> bool:
                nonlocal pause_calls
                pause_calls += 1
                return paused and pause_calls > 1

            outcome = supervise_one_wave(
                schedule=schedule,
                checkpoints=[],
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
                allocation_scheduler_state=scheduler_state(schedule),
                cooldown_required=False,
                prewave_thermal_observations=prewave,
                launch=launch,
                poll_terminal=terminal,
                observe_active=mock.Mock(),
                stop_overheated=mock.Mock(),
                now_ns=lambda: 2000,
                wait=mock.Mock(),
                pause_requested=pause,
                authorize_decision=mock.Mock(),
            )
            self.assertEqual(outcome["status"], expected)
            self.assertEqual(
                outcome["launched_allocation_ids"],
                schedule["waves"][0]["allocation_ids"],
            )
            self.assertEqual(outcome["checkpoint"]["wave_index"], 0)

    def test_supervisor_stops_only_overheated_handle_and_withholds_checkpoint(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        prewave = self.thermal_observations(
            schedule, wave_index=0, temperatures=(40, 40, 40)
        )
        polls: dict[str, int] = {}
        stopped: list[str] = []

        def launch(allocation: dict) -> WaveHandle:
            session = f"session-{allocation['allocation_id']}"
            return WaveHandle(
                allocation["allocation_id"],
                allocation["host_id"],
                f"attempt-{allocation['allocation_id']}",
                session,
                f"axeyum-smtcomp-e3-{session}.service",
            )

        def poll(handle: WaveHandle) -> dict | None:
            polls[handle.allocation_id] = polls.get(handle.allocation_id, 0) + 1
            if polls[handle.allocation_id] == 1:
                return None
            return {
                "allocation_id": handle.allocation_id,
                "attempt_id": handle.attempt_id,
                "status": "failed" if handle.host_id == "s5" else "completed",
                "terminal_record_sha256": "4" * 64,
            }

        def observe(handle: WaveHandle, observed_at_ns: int) -> dict:
            temperature = 90 if handle.host_id == "s5" else 40
            return build_thermal_observation(
                sensors_json=self.sensors_json(temperature),
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
                wave_index=0,
                allocation_id=handle.allocation_id,
                attempt_id=handle.attempt_id,
                host_id=handle.host_id,
                observed_at_ns=observed_at_ns,
            )

        def stop(handle: WaveHandle, observation: dict) -> dict:
            stopped.append(handle.allocation_id)
            return build_thermal_stop(
                observation=observation,
                session_id=handle.session_id,
                unit_prefix="axeyum-smtcomp-e3",
                exit_code=0,
                post_stop_unit_state="inactive",
                stopped_at_ns=observation["observed_at_ns"] + 1,
            )

        times = iter((2000, 2000 + 60_000_000_000))
        outcome = supervise_one_wave(
            schedule=schedule,
            checkpoints=[],
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
            allocation_scheduler_state=scheduler_state(schedule),
            cooldown_required=False,
            prewave_thermal_observations=prewave,
            launch=launch,
            poll_terminal=poll,
            observe_active=observe,
            stop_overheated=stop,
            now_ns=lambda: next(times),
            wait=lambda: None,
            pause_requested=lambda: False,
            authorize_decision=mock.Mock(),
        )
        self.assertEqual(outcome["status"], "cell-stopped")
        self.assertIsNone(outcome["checkpoint"])
        self.assertEqual(stopped, ["full-initial-00"])
        self.assertEqual(len(outcome["allocation_terminals"]), 3)

    def test_supervisor_drains_started_handle_after_partial_launch_failure(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        prewave = self.thermal_observations(
            schedule, wave_index=0, temperatures=(40, 40, 40)
        )
        launches = 0

        def launch(allocation: dict) -> WaveHandle:
            nonlocal launches
            launches += 1
            if launches == 2:
                raise OSError("fixture launch failure")
            session = f"session-{allocation['allocation_id']}"
            return WaveHandle(
                allocation["allocation_id"],
                allocation["host_id"],
                f"attempt-{allocation['allocation_id']}",
                session,
                f"axeyum-smtcomp-e3-{session}.service",
            )

        outcome = supervise_one_wave(
            schedule=schedule,
            checkpoints=[],
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
            allocation_scheduler_state=scheduler_state(schedule),
            cooldown_required=False,
            prewave_thermal_observations=prewave,
            launch=launch,
            poll_terminal=lambda handle: {
                "allocation_id": handle.allocation_id,
                "attempt_id": handle.attempt_id,
                "status": "completed",
                "terminal_record_sha256": "5" * 64,
            },
            observe_active=mock.Mock(),
            stop_overheated=mock.Mock(),
            now_ns=lambda: 2000,
            wait=mock.Mock(),
            pause_requested=lambda: False,
            authorize_decision=mock.Mock(),
        )
        self.assertEqual(outcome["status"], "cell-stopped")
        self.assertEqual(outcome["launched_allocation_ids"], ["full-initial-00"])
        self.assertEqual(len(outcome["allocation_terminals"]), 1)
        self.assertIsNone(outcome["checkpoint"])

    def test_supervisor_does_not_call_launcher_when_scheduler_blocks(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        launch = mock.Mock()
        outcome = supervise_one_wave(
            schedule=schedule,
            checkpoints=[],
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
            allocation_scheduler_state=scheduler_state(
                schedule, open_attempt_ids=["open-attempt"]
            ),
            cooldown_required=False,
            prewave_thermal_observations=[],
            launch=launch,
            poll_terminal=mock.Mock(),
            observe_active=mock.Mock(),
            stop_overheated=mock.Mock(),
            now_ns=lambda: 2000,
            wait=mock.Mock(),
            pause_requested=lambda: False,
            authorize_decision=mock.Mock(),
        )
        self.assertEqual(outcome["status"], "blocked-unclosed")
        launch.assert_not_called()

    def test_supervisor_never_launches_before_durable_authorization(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        launch = mock.Mock()

        def reject_authorization(_decision: dict) -> None:
            raise RuntimeError("authorization persistence failed")

        with self.assertRaisesRegex(RuntimeError, "persistence failed"):
            supervise_one_wave(
                schedule=schedule,
                checkpoints=[],
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
                allocation_scheduler_state=scheduler_state(schedule),
                cooldown_required=False,
                prewave_thermal_observations=self.thermal_observations(
                    schedule, wave_index=0, temperatures=(40, 40, 40)
                ),
                launch=launch,
                poll_terminal=mock.Mock(),
                observe_active=mock.Mock(),
                stop_overheated=mock.Mock(),
                now_ns=lambda: 2000,
                wait=mock.Mock(),
                pause_requested=lambda: False,
                authorize_decision=reject_authorization,
            )
        launch.assert_not_called()

    def test_readiness_requires_clean_origin_main_and_both_exact_green_gates(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            required = readiness_repository(root, DEFAULT_REQUIRED_PATHS)
            gates = [
                build_gate_observation(
                    repository_root=root,
                    command=list(command),
                    exit_code=0,
                    stdout=f"green: {command[0]}\n".encode("ascii"),
                    stderr=b"",
                    started_at_ns=1000 + index * 10,
                    ended_at_ns=1001 + index * 10,
                )
                for index, command in enumerate(
                    (("just", "check"), ("./scripts/check-smtcomp-resume.sh",))
                )
            ]
            readiness = build_readiness(
                repository_root=root,
                gate_observations=gates,
                required_paths=required,
                require_ready=True,
            )
            self.assertTrue(readiness["ready_for_live_preparation"])
            self.assertEqual(
                validate_readiness(readiness, repository_root=root)["record_sha256"],
                readiness["record_sha256"],
            )
            bad_gate = build_gate_observation(
                repository_root=root,
                command=["just", "check"],
                exit_code=1,
                stdout=b"",
                stderr=b"format drift\n",
                started_at_ns=2000,
                ended_at_ns=2001,
            )
            rejected = build_readiness(
                repository_root=root,
                gate_observations=[bad_gate, gates[1]],
                required_paths=required,
            )
            self.assertFalse(rejected["ready_for_live_preparation"])
            with self.assertRaisesRegex(ContractError, "not ready"):
                build_readiness(
                    repository_root=root,
                    gate_observations=[bad_gate, gates[1]],
                    required_paths=required,
                    require_ready=True,
                )

    def test_readiness_durable_validation_uses_recorded_git_objects(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            required = readiness_repository(root, DEFAULT_REQUIRED_PATHS)
            gates = [
                build_gate_observation(
                    repository_root=root,
                    command=list(command),
                    exit_code=0,
                    stdout=b"green\n",
                    stderr=b"",
                    started_at_ns=1000 + index * 10,
                    ended_at_ns=1001 + index * 10,
                )
                for index, command in enumerate(
                    (("just", "check"), ("./scripts/check-smtcomp-resume.sh",))
                )
            ]
            readiness = build_readiness(
                repository_root=root,
                gate_observations=gates,
                required_paths=required,
                require_ready=True,
            )
            (root / required[0]).write_text("next revision\n", encoding="utf-8")
            subprocess.run(["git", "add", required[0]], cwd=root, check=True)
            subprocess.run(
                ["git", "commit", "-m", "advance"],
                cwd=root,
                check=True,
                capture_output=True,
            )
            subprocess.run(
                ["git", "update-ref", "refs/remotes/origin/main", "HEAD"],
                cwd=root,
                check=True,
            )
            self.assertEqual(
                validate_readiness(
                    readiness,
                    repository_root=root,
                    inspect_current=False,
                )["record_sha256"],
                readiness["record_sha256"],
            )
            with self.assertRaisesRegex(ContractError, "repository drift"):
                validate_readiness(readiness, repository_root=root)

    def test_readiness_rejects_stale_gate_or_resealed_conclusion(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            required = readiness_repository(root)
            gates = [
                build_gate_observation(
                    repository_root=root,
                    command=list(command),
                    exit_code=0,
                    stdout=b"green\n",
                    stderr=b"",
                    started_at_ns=1000 + index * 10,
                    ended_at_ns=1001 + index * 10,
                )
                for index, command in enumerate(
                    (("just", "check"), ("./scripts/check-smtcomp-resume.sh",))
                )
            ]
            readiness = build_readiness(
                repository_root=root,
                gate_observations=gates,
                required_paths=required,
                fixture_only=True,
            )
            self.assertTrue(readiness["prerequisites_satisfied"])
            self.assertFalse(readiness["ready_for_live_preparation"])
            mutated = copy.deepcopy(readiness)
            mutated["ready_for_live_preparation"] = True
            with self.assertRaises(ContractError):
                validate_readiness(reseal(mutated), repository_root=root)

            (root / "untracked.txt").write_text("drift\n", encoding="utf-8")
            with self.assertRaisesRegex(ContractError, "repository state drift"):
                build_readiness(
                    repository_root=root,
                    gate_observations=gates,
                    required_paths=required,
                    fixture_only=True,
                )


if __name__ == "__main__":
    unittest.main()
