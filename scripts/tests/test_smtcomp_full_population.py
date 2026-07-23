"""Fixture gates for the credited SMT-COMP full-population contracts."""

from __future__ import annotations

import copy
import hashlib
import json
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
    validate_thermal_stop,
    validate_wave_checkpoint,
)
from full_prepare import (  # noqa: E402
    FullSolverCell,
    compose_full_cell_manifests,
    full_host_argv,
    materialize_full_selection,
    validate_full_cell_composition,
    validate_full_selection,
)
from multi_host import (  # noqa: E402
    PLAN_SCHEMA,
    REGISTRATION_SCHEMA,
    TRANSPORT,
    validate_plan,
)
from resource_enforcement import MULTI_HOST_KIND  # noqa: E402
from resume_contract import ContractError, canonical_bytes, digest  # noqa: E402
from resume_fs import read_canonical_json  # noqa: E402
from resume_runner import source_identity_artifact  # noqa: E402


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
                open_attempt_ids=[],
                failed_allocation_ids=[],
                lost_allocation_ids=[],
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
                        open_attempt_ids=[],
                        failed_allocation_ids=[],
                        lost_allocation_ids=[],
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
                open_attempt_ids=[],
                failed_allocation_ids=[],
                lost_allocation_ids=[],
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
            open_attempt_ids=[],
            failed_allocation_ids=[],
            lost_allocation_ids=[],
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
                lambda row: row["allocation_terminals"][0].__setitem__(
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
                open_attempt_ids=[],
                failed_allocation_ids=[],
                lost_allocation_ids=[],
                pause_requested=False,
                cooldown_required=False,
                thermal_observations=[],
                decided_at_ns=2000,
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
                    open_attempt_ids=opens,
                    failed_allocation_ids=failed,
                    lost_allocation_ids=lost,
                    pause_requested=pause,
                    cooldown_required=False,
                    thermal_observations=[],
                    decided_at_ns=2000,
                )
                self.assertEqual(decision["status"], expected)
                self.assertEqual(decision["allocation_ids"], [])

    def test_all_sixteen_checkpoints_close_the_cell_without_thermal_probe(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        checkpoints = [self.checkpoint(schedule, index) for index in range(WAVE_COUNT)]
        decision = scheduler_decision(
            schedule=schedule,
            checkpoints=checkpoints,
            plan_sha256=PLAN_ID,
            run_identity_sha256=RUN_ID,
            cell_id=CELL_ID,
            open_attempt_ids=[],
            failed_allocation_ids=[],
            lost_allocation_ids=[],
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
            selection_dir = shared / "selection"
            attempt = shared / "attempt"
            selection_dir.mkdir(parents=True)
            attempt.mkdir()
            accepted = accepted_fixture(shared, corpus)
            selection = materialize_full_selection(
                accepted_root=accepted,
                corpus_root=corpus,
                output_dir=selection_dir,
                fixture_only=True,
            )
            corpus_manifest = shared / "corpus.json"
            environment_manifest = shared / "environment.json"
            corpus_manifest.write_bytes(canonical_bytes({"fixture": "corpus"}))
            environment_manifest.write_bytes(canonical_bytes({"fixture": "environment"}))
            environment_sha = sha256_file(environment_manifest)
            filesystem_sha = "f" * 64
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
                        "shared_filesystem_class_sha256": filesystem_sha,
                        "environment_class_sha256": environment_sha,
                    }
                )
                for host_id in HOST_IDS
            ]
            source_identity = source_identity_artifact(ROOT, SMTCOMP)
            source_identity_path = shared / "source-identity.json"
            source_identity_path.write_bytes(canonical_bytes(source_identity))
            binaries = []
            for solver_id in SOLVER_IDS:
                binary = shared / f"{solver_id}-solver"
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
                    source_root=SMTCOMP,
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


if __name__ == "__main__":
    unittest.main()
