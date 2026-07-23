"""Frozen contracts for the credited SMT-COMP full-population run.

This module is deliberately process-free.  It constructs and validates the
selection, resource, shard, allocation, retry, and wave identities needed by
the later preparation and execution layers.  Importing it cannot probe hosts,
write shared storage, or launch a solver.
"""

from __future__ import annotations

import copy
import re
from typing import Any

from multi_host import allocation
from resume_contract import ContractError, digest


POPULATION_SCHEMA = "axeyum.smtcomp-credited-full-population.v1"
SCHEDULE_SCHEMA = "axeyum.smtcomp-credited-full-schedule.v1"
WAVE_SCHEMA = "axeyum.smtcomp-credited-full-wave.v1"

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


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _require_sha256(value: object, field: str) -> str:
    if not isinstance(value, str) or not SHA256.fullmatch(value):
        raise ContractError(f"invalid {field}")
    return value


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
