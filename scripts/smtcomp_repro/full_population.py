"""Frozen contracts for the credited SMT-COMP full-population run.

This module is deliberately process-free.  It constructs and validates the
selection, resource, shard, allocation, retry, and wave identities needed by
the later preparation and execution layers.  Importing it cannot probe hosts,
write shared storage, or launch a solver.
"""

from __future__ import annotations

import copy
import hashlib
import json
import re
from decimal import Decimal, InvalidOperation
from typing import Any

from multi_host import allocation, validate_allocation_scheduler_state
from resume_contract import ContractError, digest


POPULATION_SCHEMA = "axeyum.smtcomp-credited-full-population.v1"
SCHEDULE_SCHEMA = "axeyum.smtcomp-credited-full-schedule.v1"
WAVE_SCHEMA = "axeyum.smtcomp-credited-full-wave.v1"
THERMAL_OBSERVATION_SCHEMA = "axeyum.smtcomp-credited-full-thermal-observation.v1"
THERMAL_STOP_SCHEMA = "axeyum.smtcomp-credited-full-thermal-stop.v1"
CHECKPOINT_SCHEMA = "axeyum.smtcomp-credited-full-wave-checkpoint.v2"
SCHEDULER_DECISION_SCHEMA = "axeyum.smtcomp-credited-full-scheduler-decision.v4"

POPULATION_COUNT = 45_905
SHARD_COUNT = 96
INITIAL_ALLOCATION_COUNT = 48
RETRY_ALLOCATION_COUNT = 96
WAVE_COUNT = 16
HOST_IDS = ("s5", "s6", "s7")
SOLVER_IDS = ("axeyum", "cvc5", "bitwuzla")

FULL_LIST_SHA256 = "9d5f51d5b84c65f6c2ab03db822b185f60e47a505ec93284363dbd229305ac2b"
FULL_MANIFEST_SHA256 = (
    "8e68f29c63f11867304d5fe03eb5a2c47e0cfd15ffdcb0b5b3878dd056734791"
)
SELECTED_FILES_SHA256 = (
    "540fe29f2bc28e858b103fcd806eab709f58ed69b67d8cb95bd41bcdbaa87f39"
)

WORKERS_PER_ALLOCATION = 2
CPU_CORES_PER_ALLOCATION = 2
AGGREGATE_MEMORY_BYTES = 16 * 1024**3
MEMORY_BYTES_PER_WORKER = 8 * 1024**3
MEMORY_SWAP_BYTES = 0
PIDS_MAX = 64
WALL_LIMIT_MS = 20_000
AXEYUM_INTERNAL_TIMEOUT_MS = 19_000
THERMAL_STOP_MILLICELSIUS = 90_000
THERMAL_RESUME_MILLICELSIUS = 80_000
THERMAL_MAX_INTERVAL_NS = 60_000_000_000
THERMAL_SENSOR_CHIP = "k10temp-pci-00c3"
THERMAL_SENSOR_LABEL = "Tctl"
THERMAL_SENSOR_FIELD = "temp1_input"

SHA256 = re.compile(r"[0-9a-f]{64}\Z")
POPULATION_FIELDS = {
    "schema",
    "population_count",
    "selected_files_sha256",
    "full_list_sha256",
    "full_manifest_sha256",
    "cells",
    "record_sha256",
}
SCHEDULE_FIELDS = {
    "schema",
    "population_record_sha256",
    "enforcement_id",
    "shard_count",
    "initial_allocation_count",
    "retry_allocation_count",
    "wave_count",
    "resources",
    "allocations",
    "waves",
    "record_sha256",
}
WAVE_FIELDS = {
    "schema",
    "wave_index",
    "allocation_ids",
    "host_ids",
    "shard_ids",
    "benchmark_count",
    "record_sha256",
}
THERMAL_OBSERVATION_FIELDS = {
    "schema",
    "plan_sha256",
    "run_identity_sha256",
    "cell_id",
    "wave_index",
    "allocation_id",
    "attempt_id",
    "host_id",
    "sensor_chip",
    "sensor_label",
    "sensor_field",
    "temperature_millicelsius",
    "observed_at_ns",
    "sensors_json_sha256",
    "sensors_json_bytes",
    "record_sha256",
}
THERMAL_STOP_FIELDS = {
    "schema",
    "plan_sha256",
    "run_identity_sha256",
    "cell_id",
    "wave_index",
    "allocation_id",
    "attempt_id",
    "session_id",
    "host_id",
    "thermal_observation_record_sha256",
    "remote_unit",
    "command",
    "exit_code",
    "post_stop_unit_state",
    "stopped_at_ns",
    "record_sha256",
}
CHECKPOINT_FIELDS = {
    "schema",
    "schedule_record_sha256",
    "plan_sha256",
    "run_identity_sha256",
    "cell_id",
    "wave_index",
    "shard_completions",
    "cumulative_benchmark_count",
    "next_wave_index",
    "record_sha256",
}
CHECKPOINT_TERMINAL_FIELDS = {
    "allocation_id",
    "attempt_id",
    "status",
    "terminal_record_sha256",
}
CHECKPOINT_SHARD_COMPLETION_FIELDS = {
    "shard_id",
    "allocation_id",
    "attempt_id",
    "status",
    "terminal_record_sha256",
}
SCHEDULER_DECISION_FIELDS = {
    "schema",
    "schedule_record_sha256",
    "plan_sha256",
    "run_identity_sha256",
    "cell_id",
    "allocation_scheduler_state_sha256",
    "status",
    "completed_checkpoint_sha256s",
    "next_wave_index",
    "allocation_ids",
    "open_attempt_ids",
    "uncheckpointed_completed_allocation_ids",
    "recovery_checkpoint",
    "failed_allocation_ids",
    "lost_allocation_ids",
    "pause_requested",
    "cooldown_required",
    "thermal_observation_sha256s",
    "decided_at_ns",
    "record_sha256",
}
SAFE_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}\Z")
SAFE_UNIT_PREFIX = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,63}\Z")


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _require_sha256(value: object, field: str) -> str:
    if not isinstance(value, str) or not SHA256.fullmatch(value):
        raise ContractError(f"invalid {field}")
    return value


def _require_safe_id(value: object, field: str) -> str:
    if not isinstance(value, str) or not SAFE_ID.fullmatch(value):
        raise ContractError(f"invalid {field}")
    return value


def _validate_seal(value: dict[str, Any]) -> None:
    expected = value.get("record_sha256")
    if not isinstance(expected, str) or expected != _sealed(value)["record_sha256"]:
        raise ContractError("record seal mismatch")


def shard_benchmark_count(shard_id: int) -> int:
    """Return the striped-shard population fixed by 45,905 rows / 96 shards."""

    if type(shard_id) is not int or not 0 <= shard_id < SHARD_COUNT:
        raise ContractError("invalid full-population shard ID")
    return 479 if shard_id <= 16 else 478


def build_population_contract() -> dict[str, Any]:
    """Build the one-selection, three-cell identity contract."""

    cells = [
        {
            "solver_id": solver_id,
            "population_count": POPULATION_COUNT,
            "full_list_sha256": FULL_LIST_SHA256,
            "full_manifest_sha256": FULL_MANIFEST_SHA256,
        }
        for solver_id in SOLVER_IDS
    ]
    return _sealed(
        {
            "schema": POPULATION_SCHEMA,
            "population_count": POPULATION_COUNT,
            "selected_files_sha256": SELECTED_FILES_SHA256,
            "full_list_sha256": FULL_LIST_SHA256,
            "full_manifest_sha256": FULL_MANIFEST_SHA256,
            "cells": cells,
        }
    )


def validate_population_contract(contract: dict[str, Any]) -> dict[str, Any]:
    """Reject any population, order, manifest, or solver-cell drift."""

    if set(contract) != POPULATION_FIELDS or contract.get("schema") != POPULATION_SCHEMA:
        raise ContractError("full-population field/schema mismatch")
    if contract != build_population_contract():
        raise ContractError("full-population identity differs from preregistration")
    return contract


def _retry_host(initial_host: str, shard_id: int) -> str:
    alternatives = {
        "s5": ("s6", "s7"),
        "s6": ("s7", "s5"),
        "s7": ("s5", "s6"),
    }
    try:
        return alternatives[initial_host][shard_id % 2]
    except KeyError as exc:
        raise ContractError("unknown initial host in retry schedule") from exc


def build_allocations(enforcement_id: str) -> list[dict[str, Any]]:
    """Build 48 two-shard initial allocations and 96 exact-shard retries."""

    _require_sha256(enforcement_id, "enforcement_id")
    initial = [
        allocation(
            allocation_id=f"full-initial-{index:02d}",
            generation=0,
            host_id=HOST_IDS[index % len(HOST_IDS)],
            shard_ids=[2 * index, 2 * index + 1],
            enforcement_id=enforcement_id,
        )
        for index in range(INITIAL_ALLOCATION_COUNT)
    ]
    retries = []
    for shard_id in range(SHARD_COUNT):
        owner_index = shard_id // 2
        owner = initial[owner_index]
        retries.append(
            allocation(
                allocation_id=f"full-retry-{shard_id:02d}",
                generation=1,
                host_id=_retry_host(owner["host_id"], shard_id),
                shard_ids=[shard_id],
                enforcement_id=enforcement_id,
                recovers_allocation_id=owner["allocation_id"],
            )
        )
    return initial + retries


def _build_waves(initial_allocations: list[dict[str, Any]]) -> list[dict[str, Any]]:
    waves = []
    for wave_index in range(WAVE_COUNT):
        rows = initial_allocations[3 * wave_index : 3 * wave_index + 3]
        shard_ids = [shard for row in rows for shard in row["shard_ids"]]
        waves.append(
            _sealed(
                {
                    "schema": WAVE_SCHEMA,
                    "wave_index": wave_index,
                    "allocation_ids": [row["allocation_id"] for row in rows],
                    "host_ids": [row["host_id"] for row in rows],
                    "shard_ids": shard_ids,
                    "benchmark_count": sum(
                        shard_benchmark_count(shard_id) for shard_id in shard_ids
                    ),
                }
            )
        )
    return waves


def build_schedule(enforcement_id: str) -> dict[str, Any]:
    """Build the immutable allocation/resource/wave schedule."""

    allocations = build_allocations(enforcement_id)
    resources = {
        "workers_per_allocation": WORKERS_PER_ALLOCATION,
        "cpu_cores_per_allocation": CPU_CORES_PER_ALLOCATION,
        "aggregate_memory_bytes": AGGREGATE_MEMORY_BYTES,
        "memory_bytes_per_worker": MEMORY_BYTES_PER_WORKER,
        "memory_swap_bytes": MEMORY_SWAP_BYTES,
        "pids_max": PIDS_MAX,
        "wall_limit_ms": WALL_LIMIT_MS,
        "axeyum_internal_timeout_ms": AXEYUM_INTERNAL_TIMEOUT_MS,
        "solver_environment": {
            "AYU_THREADS": "1",
            "OMP_NUM_THREADS": "1",
            "RAYON_NUM_THREADS": "1",
        },
    }
    return _sealed(
        {
            "schema": SCHEDULE_SCHEMA,
            "population_record_sha256": build_population_contract()["record_sha256"],
            "enforcement_id": enforcement_id,
            "shard_count": SHARD_COUNT,
            "initial_allocation_count": INITIAL_ALLOCATION_COUNT,
            "retry_allocation_count": RETRY_ALLOCATION_COUNT,
            "wave_count": WAVE_COUNT,
            "resources": resources,
            "allocations": allocations,
            "waves": _build_waves(allocations[:INITIAL_ALLOCATION_COUNT]),
        }
    )


def validate_schedule(schedule: dict[str, Any]) -> dict[str, Any]:
    """Reject schedule/resource/retry drift against the frozen construction."""

    if set(schedule) != SCHEDULE_FIELDS or schedule.get("schema") != SCHEDULE_SCHEMA:
        raise ContractError("full-population schedule field/schema mismatch")
    enforcement_id = _require_sha256(schedule.get("enforcement_id"), "enforcement_id")
    expected = build_schedule(enforcement_id)
    if schedule != expected:
        raise ContractError("full-population schedule differs from preregistration")
    for wave in schedule["waves"]:
        if set(wave) != WAVE_FIELDS or wave.get("schema") != WAVE_SCHEMA:
            raise ContractError("full-population wave field/schema mismatch")
    return schedule


def _unique_json_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ContractError("duplicate key in sensors JSON")
        result[key] = value
    return result


def _reject_json_constant(value: str) -> None:
    raise ContractError(f"non-finite constant in sensors JSON: {value}")


def _parse_sensors_json(raw: bytes) -> tuple[dict[str, Any], int]:
    try:
        decoded = raw.decode("utf-8")
        payload = json.loads(
            decoded,
            object_pairs_hook=_unique_json_object,
            parse_constant=_reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError("malformed sensors JSON") from exc
    if not isinstance(payload, dict):
        raise ContractError("sensors JSON root must be an object")
    try:
        value = payload[THERMAL_SENSOR_CHIP][THERMAL_SENSOR_LABEL][
            THERMAL_SENSOR_FIELD
        ]
    except (KeyError, TypeError) as exc:
        raise ContractError("required CPU thermal sensor is missing") from exc
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ContractError("CPU thermal sensor value is not numeric")
    try:
        millicelsius = Decimal(str(value)) * 1000
    except InvalidOperation as exc:
        raise ContractError("CPU thermal sensor value is invalid") from exc
    if not millicelsius.is_finite() or millicelsius != millicelsius.to_integral_value():
        raise ContractError("CPU thermal sensor lacks exact millidegree precision")
    result = int(millicelsius)
    if not 0 <= result <= 150_000:
        raise ContractError("CPU thermal sensor value is outside the accepted range")
    return payload, result


def build_thermal_observation(
    *,
    sensors_json: bytes,
    plan_sha256: str,
    run_identity_sha256: str,
    cell_id: str,
    wave_index: int,
    allocation_id: str,
    attempt_id: str | None,
    host_id: str,
    observed_at_ns: int,
) -> dict[str, Any]:
    """Parse and seal one exact-source ``sensors -j`` observation."""

    if not isinstance(sensors_json, bytes) or not sensors_json:
        raise ContractError("sensors JSON must be non-empty bytes")
    _payload, millicelsius = _parse_sensors_json(sensors_json)
    observation = _sealed(
        {
            "schema": THERMAL_OBSERVATION_SCHEMA,
            "plan_sha256": _require_sha256(plan_sha256, "plan_sha256"),
            "run_identity_sha256": _require_sha256(
                run_identity_sha256, "run_identity_sha256"
            ),
            "cell_id": _require_safe_id(cell_id, "cell_id"),
            "wave_index": wave_index,
            "allocation_id": _require_safe_id(allocation_id, "allocation_id"),
            "attempt_id": (
                None
                if attempt_id is None
                else _require_safe_id(attempt_id, "attempt_id")
            ),
            "host_id": _require_safe_id(host_id, "host_id"),
            "sensor_chip": THERMAL_SENSOR_CHIP,
            "sensor_label": THERMAL_SENSOR_LABEL,
            "sensor_field": THERMAL_SENSOR_FIELD,
            "temperature_millicelsius": millicelsius,
            "observed_at_ns": observed_at_ns,
            "sensors_json_sha256": hashlib.sha256(sensors_json).hexdigest(),
            "sensors_json_bytes": len(sensors_json),
        }
    )
    return validate_thermal_observation(observation)


def validate_thermal_observation(observation: dict[str, Any]) -> dict[str, Any]:
    if (
        set(observation) != THERMAL_OBSERVATION_FIELDS
        or observation.get("schema") != THERMAL_OBSERVATION_SCHEMA
    ):
        raise ContractError("thermal observation field/schema mismatch")
    _validate_seal(observation)
    for field in ("plan_sha256", "run_identity_sha256", "sensors_json_sha256"):
        _require_sha256(observation.get(field), field)
    for field in ("cell_id", "allocation_id", "host_id"):
        _require_safe_id(observation.get(field), field)
    attempt_id = observation.get("attempt_id")
    if attempt_id is not None:
        _require_safe_id(attempt_id, "attempt_id")
    if (
        type(observation.get("wave_index")) is not int
        or not 0 <= observation["wave_index"] < WAVE_COUNT
        or type(observation.get("observed_at_ns")) is not int
        or observation["observed_at_ns"] <= 0
        or type(observation.get("temperature_millicelsius")) is not int
        or not 0 <= observation["temperature_millicelsius"] <= 150_000
        or type(observation.get("sensors_json_bytes")) is not int
        or observation["sensors_json_bytes"] <= 0
    ):
        raise ContractError("thermal observation numeric field mismatch")
    if (
        observation["sensor_chip"] != THERMAL_SENSOR_CHIP
        or observation["sensor_label"] != THERMAL_SENSOR_LABEL
        or observation["sensor_field"] != THERMAL_SENSOR_FIELD
        or observation["host_id"] not in HOST_IDS
    ):
        raise ContractError("thermal observation source/host mismatch")
    return observation


def _validate_thermal_launch_set(
    *,
    observations: list[dict[str, Any]],
    schedule: dict[str, Any],
    plan_sha256: str,
    run_identity_sha256: str,
    cell_id: str,
    wave_index: int,
    cooldown_required: bool,
    decided_at_ns: int,
) -> tuple[bool, str, list[str]]:
    if type(cooldown_required) is not bool:
        raise ContractError("cooldown_required must be Boolean")
    wave = schedule["waves"][wave_index]
    expected = dict(zip(wave["host_ids"], wave["allocation_ids"], strict=True))
    by_host: dict[str, dict[str, Any]] = {}
    for observation in observations:
        validate_thermal_observation(observation)
        host_id = observation["host_id"]
        if host_id in by_host:
            raise ContractError("duplicate host thermal observation")
        if (
            observation["plan_sha256"] != plan_sha256
            or observation["run_identity_sha256"] != run_identity_sha256
            or observation["cell_id"] != cell_id
            or observation["wave_index"] != wave_index
            or observation["allocation_id"] != expected.get(host_id)
            or observation["attempt_id"] is not None
            or observation["observed_at_ns"] > decided_at_ns
            or decided_at_ns - observation["observed_at_ns"] > THERMAL_MAX_INTERVAL_NS
        ):
            raise ContractError("pre-wave thermal observation identity mismatch")
        by_host[host_id] = observation
    if set(by_host) != set(HOST_IDS):
        raise ContractError("pre-wave thermal observations do not cover every host")
    record_ids = [by_host[host]["record_sha256"] for host in HOST_IDS]
    temperatures = [by_host[host]["temperature_millicelsius"] for host in HOST_IDS]
    if any(value >= THERMAL_STOP_MILLICELSIUS for value in temperatures):
        return False, "thermal-stop-required", record_ids
    if cooldown_required and any(
        value >= THERMAL_RESUME_MILLICELSIUS for value in temperatures
    ):
        return False, "thermal-cooldown", record_ids
    return True, "launch", record_ids


def build_thermal_stop(
    *,
    observation: dict[str, Any],
    session_id: str,
    unit_prefix: str,
    exit_code: int,
    post_stop_unit_state: str,
    stopped_at_ns: int,
) -> dict[str, Any]:
    """Seal proof that only an overheated allocation's registered unit stopped."""

    validate_thermal_observation(observation)
    if observation["temperature_millicelsius"] < THERMAL_STOP_MILLICELSIUS:
        raise ContractError("thermal stop requires an at-threshold observation")
    if observation["attempt_id"] is None:
        raise ContractError("thermal stop requires an active allocation attempt")
    session = _require_safe_id(session_id, "session_id")
    if not SAFE_UNIT_PREFIX.fullmatch(unit_prefix):
        raise ContractError("invalid thermal-stop unit prefix")
    remote_unit = f"{unit_prefix}-{session}.service"
    record = _sealed(
        {
            "schema": THERMAL_STOP_SCHEMA,
            "plan_sha256": observation["plan_sha256"],
            "run_identity_sha256": observation["run_identity_sha256"],
            "cell_id": observation["cell_id"],
            "wave_index": observation["wave_index"],
            "allocation_id": observation["allocation_id"],
            "attempt_id": observation["attempt_id"],
            "session_id": session,
            "host_id": observation["host_id"],
            "thermal_observation_record_sha256": observation["record_sha256"],
            "remote_unit": remote_unit,
            "command": ["systemctl", "--user", "stop", remote_unit],
            "exit_code": exit_code,
            "post_stop_unit_state": post_stop_unit_state,
            "stopped_at_ns": stopped_at_ns,
        }
    )
    return validate_thermal_stop(
        record,
        observation=observation,
        session_id=session,
        unit_prefix=unit_prefix,
    )


def validate_thermal_stop(
    record: dict[str, Any],
    *,
    observation: dict[str, Any],
    session_id: str,
    unit_prefix: str,
) -> dict[str, Any]:
    validate_thermal_observation(observation)
    if set(record) != THERMAL_STOP_FIELDS or record.get("schema") != THERMAL_STOP_SCHEMA:
        raise ContractError("thermal-stop field/schema mismatch")
    _validate_seal(record)
    session = _require_safe_id(session_id, "session_id")
    if not SAFE_UNIT_PREFIX.fullmatch(unit_prefix):
        raise ContractError("invalid thermal-stop unit prefix")
    expected_unit = f"{unit_prefix}-{session}.service"
    identity_fields = (
        "plan_sha256",
        "run_identity_sha256",
        "cell_id",
        "wave_index",
        "allocation_id",
        "attempt_id",
        "host_id",
    )
    if any(record[field] != observation[field] for field in identity_fields):
        raise ContractError("thermal-stop observation identity mismatch")
    if (
        observation["temperature_millicelsius"] < THERMAL_STOP_MILLICELSIUS
        or record["thermal_observation_record_sha256"]
        != observation["record_sha256"]
        or record["session_id"] != session
        or record["remote_unit"] != expected_unit
        or record["command"] != ["systemctl", "--user", "stop", expected_unit]
        or record["exit_code"] != 0
        or record["post_stop_unit_state"] not in {"inactive", "failed"}
        or type(record["stopped_at_ns"]) is not int
        or record["stopped_at_ns"] <= observation["observed_at_ns"]
    ):
        raise ContractError("thermal-stop exact-unit evidence mismatch")
    return record


def cumulative_benchmark_count(schedule: dict[str, Any], wave_index: int) -> int:
    validate_schedule(schedule)
    if type(wave_index) is not int or not 0 <= wave_index < WAVE_COUNT:
        raise ContractError("invalid checkpoint wave index")
    return sum(
        wave["benchmark_count"] for wave in schedule["waves"][: wave_index + 1]
    )


def build_wave_checkpoint(
    *,
    schedule: dict[str, Any],
    plan_sha256: str,
    run_identity_sha256: str,
    cell_id: str,
    wave_index: int,
    allocation_terminals: list[dict[str, Any]],
    cumulative_records: int,
) -> dict[str, Any]:
    """Build derived restart state after every wave shard is complete.

    A shard may be closed either by its preregistered initial allocation or by
    its one exact different-host retry.  This is deliberately shard-granular:
    one failed two-shard initial allocation requires two independently proven
    retry terminals before its wave can rejoin the checkpoint chain.
    """

    validate_schedule(schedule)
    if type(wave_index) is not int or not 0 <= wave_index < WAVE_COUNT:
        raise ContractError("invalid checkpoint wave index")
    wave = schedule["waves"][wave_index]
    expected_shards = wave["shard_ids"]
    allocations = {
        row["allocation_id"]: row for row in schedule["allocations"]
    }
    initial_owner = {
        shard_id: allocation_id
        for allocation_id in wave["allocation_ids"]
        for shard_id in allocations[allocation_id]["shard_ids"]
    }
    by_shard: dict[int, dict[str, Any]] = {}
    for terminal in allocation_terminals:
        if set(terminal) != CHECKPOINT_TERMINAL_FIELDS:
            raise ContractError("checkpoint terminal field mismatch")
        allocation_id = _require_safe_id(terminal.get("allocation_id"), "allocation_id")
        allocation = allocations.get(allocation_id)
        if allocation is None:
            raise ContractError("checkpoint names an unknown allocation")
        _require_safe_id(terminal.get("attempt_id"), "attempt_id")
        _require_sha256(terminal.get("terminal_record_sha256"), "terminal_record_sha256")
        if terminal.get("status") != "completed":
            raise ContractError("checkpoint cannot include a failed allocation")
        for shard_id in allocation["shard_ids"]:
            owner = initial_owner.get(shard_id)
            if owner is None or (
                allocation_id != owner
                and not (
                    allocation["generation"] == 1
                    and allocation["recovers_allocation_id"] == owner
                )
            ):
                raise ContractError("checkpoint allocation is not valid for wave shard")
            if shard_id in by_shard:
                raise ContractError("duplicate checkpoint shard completion")
            by_shard[shard_id] = {
                "shard_id": shard_id,
                **copy.deepcopy(terminal),
            }
    if set(by_shard) != set(expected_shards):
        raise ContractError("checkpoint does not close every exact wave shard")
    expected_records = cumulative_benchmark_count(schedule, wave_index)
    if cumulative_records != expected_records:
        raise ContractError("checkpoint cumulative population mismatch")
    record = _sealed(
        {
            "schema": CHECKPOINT_SCHEMA,
            "schedule_record_sha256": schedule["record_sha256"],
            "plan_sha256": _require_sha256(plan_sha256, "plan_sha256"),
            "run_identity_sha256": _require_sha256(
                run_identity_sha256, "run_identity_sha256"
            ),
            "cell_id": _require_safe_id(cell_id, "cell_id"),
            "wave_index": wave_index,
            "shard_completions": [by_shard[value] for value in expected_shards],
            "cumulative_benchmark_count": cumulative_records,
            "next_wave_index": wave_index + 1 if wave_index + 1 < WAVE_COUNT else None,
        }
    )
    return validate_wave_checkpoint(
        record,
        schedule=schedule,
        plan_sha256=plan_sha256,
        run_identity_sha256=run_identity_sha256,
        cell_id=cell_id,
    )


def validate_wave_checkpoint(
    checkpoint: dict[str, Any],
    *,
    schedule: dict[str, Any],
    plan_sha256: str,
    run_identity_sha256: str,
    cell_id: str,
) -> dict[str, Any]:
    validate_schedule(schedule)
    if set(checkpoint) != CHECKPOINT_FIELDS or checkpoint.get("schema") != CHECKPOINT_SCHEMA:
        raise ContractError("wave checkpoint field/schema mismatch")
    _validate_seal(checkpoint)
    if (
        checkpoint["schedule_record_sha256"] != schedule["record_sha256"]
        or checkpoint["plan_sha256"] != _require_sha256(plan_sha256, "plan_sha256")
        or checkpoint["run_identity_sha256"]
        != _require_sha256(run_identity_sha256, "run_identity_sha256")
        or checkpoint["cell_id"] != _require_safe_id(cell_id, "cell_id")
    ):
        raise ContractError("wave checkpoint run identity mismatch")
    wave_index = checkpoint.get("wave_index")
    if type(wave_index) is not int or not 0 <= wave_index < WAVE_COUNT:
        raise ContractError("invalid checkpoint wave index")
    completions = checkpoint.get("shard_completions")
    if not isinstance(completions, list):
        raise ContractError("checkpoint shard completions must be a list")
    wave = schedule["waves"][wave_index]
    expected_shards = wave["shard_ids"]
    if [row.get("shard_id") for row in completions] != expected_shards:
        raise ContractError("checkpoint shard order/identity mismatch")
    allocations = {
        row["allocation_id"]: row for row in schedule["allocations"]
    }
    initial_owner = {
        shard_id: allocation_id
        for allocation_id in wave["allocation_ids"]
        for shard_id in allocations[allocation_id]["shard_ids"]
    }
    for completion in completions:
        if set(completion) != CHECKPOINT_SHARD_COMPLETION_FIELDS:
            raise ContractError("checkpoint shard completion field mismatch")
        allocation_id = _require_safe_id(
            completion.get("allocation_id"), "allocation_id"
        )
        allocation = allocations.get(allocation_id)
        shard_id = completion.get("shard_id")
        owner = initial_owner.get(shard_id)
        if (
            allocation is None
            or type(shard_id) is not int
            or shard_id not in allocation["shard_ids"]
            or owner is None
            or (
                allocation_id != owner
                and not (
                    allocation["generation"] == 1
                    and allocation["recovers_allocation_id"] == owner
                )
            )
        ):
            raise ContractError("checkpoint allocation is not valid for wave shard")
        _require_safe_id(completion.get("attempt_id"), "attempt_id")
        _require_sha256(
            completion.get("terminal_record_sha256"), "terminal_record_sha256"
        )
        if completion.get("status") != "completed":
            raise ContractError("checkpoint includes non-completed shard")
    expected_count = cumulative_benchmark_count(schedule, wave_index)
    expected_next = wave_index + 1 if wave_index + 1 < WAVE_COUNT else None
    if (
        checkpoint["cumulative_benchmark_count"] != expected_count
        or checkpoint["next_wave_index"] != expected_next
    ):
        raise ContractError("wave checkpoint count/continuation mismatch")
    return checkpoint


def validate_checkpoint_chain(
    checkpoints: list[dict[str, Any]],
    *,
    schedule: dict[str, Any],
    plan_sha256: str,
    run_identity_sha256: str,
    cell_id: str,
) -> list[dict[str, Any]]:
    if not isinstance(checkpoints, list) or len(checkpoints) > WAVE_COUNT:
        raise ContractError("invalid wave checkpoint chain")
    for expected_index, checkpoint in enumerate(checkpoints):
        validate_wave_checkpoint(
            checkpoint,
            schedule=schedule,
            plan_sha256=plan_sha256,
            run_identity_sha256=run_identity_sha256,
            cell_id=cell_id,
        )
        if checkpoint["wave_index"] != expected_index:
            raise ContractError("wave checkpoint chain is not a contiguous prefix")
    return checkpoints


def scheduler_decision(
    *,
    schedule: dict[str, Any],
    checkpoints: list[dict[str, Any]],
    plan_sha256: str,
    run_identity_sha256: str,
    cell_id: str,
    allocation_scheduler_state: dict[str, Any],
    pause_requested: bool,
    cooldown_required: bool,
    thermal_observations: list[dict[str, Any]],
    decided_at_ns: int,
) -> dict[str, Any]:
    """Return the only permitted next action from durable scheduler state."""

    validate_schedule(schedule)
    plan = _require_sha256(plan_sha256, "plan_sha256")
    run = _require_sha256(run_identity_sha256, "run_identity_sha256")
    cell = _require_safe_id(cell_id, "cell_id")
    allocation_state = validate_allocation_scheduler_state(
        allocation_scheduler_state,
        plan_sha256=plan,
        run_identity_sha256=run,
        cell_id=cell,
        allocation_ids={row["allocation_id"] for row in schedule["allocations"]},
    )
    validate_checkpoint_chain(
        checkpoints,
        schedule=schedule,
        plan_sha256=plan,
        run_identity_sha256=run,
        cell_id=cell,
    )
    opens = allocation_state["open_attempt_ids"]
    completed = set(allocation_state["completed_allocation_ids"])
    failed = allocation_state["failed_allocation_ids"]
    lost = allocation_state["lost_allocation_ids"]
    if type(pause_requested) is not bool or type(cooldown_required) is not bool:
        raise ContractError("scheduler flags must be Boolean")
    if type(decided_at_ns) is not int or decided_at_ns <= 0:
        raise ContractError("invalid scheduler decision time")
    initial_ids = {
        row["allocation_id"]
        for row in schedule["allocations"]
        if row["generation"] == 0
    }
    if not set(failed + lost) <= initial_ids:
        raise ContractError("scheduler failure names a non-initial allocation")

    next_wave = len(checkpoints) if len(checkpoints) < WAVE_COUNT else None
    checkpointed_allocations = {
        row["allocation_id"]
        for checkpoint in checkpoints
        for row in checkpoint["shard_completions"]
    }
    if not checkpointed_allocations <= completed:
        raise ContractError(
            "scheduler checkpoint names an allocation without a completed terminal"
        )
    checkpointed_shards = {
        row["shard_id"]
        for checkpoint in checkpoints
        for row in checkpoint["shard_completions"]
    }
    allocations_by_id = {
        row["allocation_id"]: row for row in schedule["allocations"]
    }
    failed = [
        allocation_id
        for allocation_id in failed
        if not set(allocations_by_id[allocation_id]["shard_ids"])
        <= checkpointed_shards
    ]
    lost = [
        allocation_id
        for allocation_id in lost
        if not set(allocations_by_id[allocation_id]["shard_ids"])
        <= checkpointed_shards
    ]
    uncheckpointed_completed = sorted(completed - checkpointed_allocations)
    recovery_checkpoint = None
    if uncheckpointed_completed and not opens and next_wave is not None:
        wave = schedule["waves"][next_wave]
        allocations = allocations_by_id
        initial_ids_for_wave = set(wave["allocation_ids"])
        eligible_ids = initial_ids_for_wave | {
            allocation_id
            for allocation_id, allocation in allocations.items()
            if allocation["generation"] == 1
            and allocation["recovers_allocation_id"] in initial_ids_for_wave
        }
        terminals = [
            {
                "allocation_id": row["allocation_id"],
                "attempt_id": row["attempt_id"],
                "status": "completed",
                "terminal_record_sha256": row["terminal_record_sha256"],
            }
            for row in allocation_state["allocation_attempts"]
            if row["terminal_status"] == "completed"
            and row["allocation_id"] in eligible_ids
        ]
        covered_shards: set[int] = set()
        ambiguous = False
        for terminal in terminals:
            for shard_id in allocations[terminal["allocation_id"]]["shard_ids"]:
                if shard_id in wave["shard_ids"]:
                    if shard_id in covered_shards:
                        ambiguous = True
                    covered_shards.add(shard_id)
        if ambiguous:
            raise ContractError("scheduler recovery has ambiguous shard completion")
        if covered_shards == set(wave["shard_ids"]):
            recovery_checkpoint = build_wave_checkpoint(
                schedule=schedule,
                plan_sha256=plan,
                run_identity_sha256=run,
                cell_id=cell,
                wave_index=next_wave,
                allocation_terminals=terminals,
                cumulative_records=cumulative_benchmark_count(schedule, next_wave),
            )
    status: str
    allocation_ids: list[str] = []
    thermal_ids: list[str] = []
    if opens:
        status = "blocked-unclosed"
    elif recovery_checkpoint is not None:
        status = "recover-checkpoint"
    elif uncheckpointed_completed:
        status = "blocked-uncheckpointed"
    elif failed or lost:
        status = "blocked-failure"
    elif pause_requested:
        status = "paused"
    elif next_wave is None:
        status = "complete"
    else:
        permitted, thermal_status, thermal_ids = _validate_thermal_launch_set(
            observations=thermal_observations,
            schedule=schedule,
            plan_sha256=plan,
            run_identity_sha256=run,
            cell_id=cell,
            wave_index=next_wave,
            cooldown_required=cooldown_required,
            decided_at_ns=decided_at_ns,
        )
        status = "launch" if permitted else thermal_status
        if permitted:
            allocation_ids = schedule["waves"][next_wave]["allocation_ids"]
    decision = _sealed(
        {
            "schema": SCHEDULER_DECISION_SCHEMA,
            "schedule_record_sha256": schedule["record_sha256"],
            "plan_sha256": plan,
            "run_identity_sha256": run,
            "cell_id": cell,
            "allocation_scheduler_state_sha256": allocation_state["record_sha256"],
            "status": status,
            "completed_checkpoint_sha256s": [
                checkpoint["record_sha256"] for checkpoint in checkpoints
            ],
            "next_wave_index": next_wave,
            "allocation_ids": allocation_ids,
            "open_attempt_ids": opens,
            "uncheckpointed_completed_allocation_ids": uncheckpointed_completed,
            "recovery_checkpoint": recovery_checkpoint,
            "failed_allocation_ids": failed,
            "lost_allocation_ids": lost,
            "pause_requested": pause_requested,
            "cooldown_required": cooldown_required,
            "thermal_observation_sha256s": thermal_ids,
            "decided_at_ns": decided_at_ns,
        }
    )
    if set(decision) != SCHEDULER_DECISION_FIELDS:
        raise AssertionError("internal scheduler decision field drift")
    return decision
