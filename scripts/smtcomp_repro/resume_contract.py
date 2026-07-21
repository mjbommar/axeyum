"""Executable prototype for the distributed SMT-COMP resume contract.

This module models immutable per-result checkpoints, exact run identity,
attempt accounting, shard completion, and strict canonical merge.  It is a
planning prototype, not the production remote runner.
"""

from __future__ import annotations

import copy
import hashlib
import json
from dataclasses import dataclass
from typing import Any


RUN_SCHEMA = "axeyum.smtcomp-run.v1"
RESULT_SCHEMA = "axeyum.smtcomp-result.v1"
RUN_IDENTITY_FIELDS = {
    "contract_schema",
    "benchmark_schema",
    "selection_manifest_sha256",
    "selected_list_sha256",
    "corpus_identity_sha256",
    "solver_binary_sha256",
    "solver_command_sha256",
    "runner_source_sha256",
    "repository_commit",
    "track",
    "wall_limit_ms",
    "cpu_limit_ms",
    "memory_limit_bytes",
    "cores",
    "shard_count",
    "shard_mapping",
    "environment_class_sha256",
}
RESULT_RECORD_FIELDS = {
    "schema",
    "run_identity_sha256",
    "result_key",
    "benchmark_id",
    "benchmark_sha256",
    "solver_id",
    "shard_id",
    "sequence",
    "environment_class_sha256",
    "expected_status",
    "reported_status",
    "wall_time_ns",
    "cpu_time_ns",
    "record_sha256",
}
ATTEMPT_LAUNCH_FIELDS = {
    "attempt_id",
    "run_identity_sha256",
    "shard_id",
    "host_id",
    "pid",
    "assigned_count",
    "launched_at_ns",
    "enforcement_id",
    "environment_class_sha256",
    "terminal",
}
ATTEMPT_TERMINAL_FIELDS = {
    "status",
    "exit_code",
    "signal",
    "wall_time_ns",
    "peak_rss_bytes",
    "completed_count",
    "result_set_sha256",
    "missing_result_keys",
    "ended_at_ns",
}
SHARD_COMPLETION_FIELDS = {
    "state",
    "run_identity_sha256",
    "assigned_count",
    "completed_count",
    "missing_result_keys",
    "result_set_sha256",
    "attempt_ids",
    "unclosed_attempt_ids",
}


class ContractError(ValueError):
    """A fail-closed contract violation."""


def canonical_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def result_key(benchmark_id: str, benchmark_sha256: str, solver_id: str) -> str:
    return digest(
        {
            "benchmark_id": benchmark_id,
            "benchmark_sha256": benchmark_sha256,
            "solver_id": solver_id,
        }
    )


def seal_record(record: dict[str, Any]) -> dict[str, Any]:
    sealed = copy.deepcopy(record)
    sealed.pop("record_sha256", None)
    sealed["record_sha256"] = digest(sealed)
    return sealed


def validate_record(record: dict[str, Any], run_identity_sha256: str) -> None:
    if set(record) != RESULT_RECORD_FIELDS:
        raise ContractError("record field set mismatch")
    if record["schema"] != RESULT_SCHEMA:
        raise ContractError("record schema mismatch")
    if record["run_identity_sha256"] != run_identity_sha256:
        raise ContractError("record run identity mismatch")
    expected_key = result_key(
        record["benchmark_id"], record["benchmark_sha256"], record["solver_id"]
    )
    if record["result_key"] != expected_key:
        raise ContractError("result key mismatch")
    unsealed = copy.deepcopy(record)
    claimed = unsealed.pop("record_sha256")
    if claimed != digest(unsealed):
        raise ContractError("record hash mismatch")


def record_set_sha256(records: list[dict[str, Any]]) -> str:
    return digest(
        [
            {"result_key": row["result_key"], "record_sha256": row["record_sha256"]}
            for row in sorted(records, key=lambda row: row["result_key"])
        ]
    )


@dataclass
class Bundle:
    run: dict[str, Any]
    assignments: list[dict[str, Any]]
    records: list[dict[str, Any]]
    attempts: dict[str, list[dict[str, Any]]]
    completions: dict[str, dict[str, Any]]


def _validate_resources(run: dict[str, Any]) -> None:
    resources = run.get("resource_enforcement")
    if not resources or resources.get("kind") in (None, "none"):
        raise ContractError("missing aggregate resource enforcement")
    if not resources.get("enforcement_id"):
        raise ContractError("missing resource enforcement identity")
    aggregate = resources.get("aggregate_memory_bytes", 0)
    workers = resources.get("worker_slots", 0)
    per_worker = run["identity"].get("memory_limit_bytes", 0)
    if workers <= 0 or aggregate <= 0 or workers * per_worker > aggregate:
        raise ContractError("aggregate memory budget overcommitted")


def merge_complete(bundle: Bundle) -> bytes:
    """Validate a complete bundle and return canonical raw-result bytes."""
    run = bundle.run
    if run.get("schema") != RUN_SCHEMA:
        raise ContractError("run schema mismatch")
    identity = run.get("identity")
    if not isinstance(identity, dict) or run.get("identity_sha256") != digest(identity):
        raise ContractError("run identity mismatch")
    if set(identity) != RUN_IDENTITY_FIELDS:
        raise ContractError("run identity field set mismatch")
    if identity["contract_schema"] != "axeyum.smtcomp-resumable-run-contract.v1":
        raise ContractError("contract schema mismatch")
    if identity["benchmark_schema"] != RESULT_SCHEMA:
        raise ContractError("benchmark schema mismatch")
    run_hash = run["identity_sha256"]
    _validate_resources(run)

    assigned_owner: dict[str, str] = {}
    assignments_by_shard: dict[str, set[str]] = {}
    for assignment in bundle.assignments:
        shard_id = assignment["shard_id"]
        if shard_id in assignments_by_shard:
            raise ContractError("duplicate shard assignment")
        keys = set(assignment["result_keys"])
        if len(keys) != len(assignment["result_keys"]):
            raise ContractError("duplicate key within shard assignment")
        assignments_by_shard[shard_id] = keys
        for key in keys:
            if key in assigned_owner:
                raise ContractError("overlapping shard assignment")
            assigned_owner[key] = shard_id
    if len(assignments_by_shard) != identity["shard_count"]:
        raise ContractError("shard count mismatch")

    by_shard: dict[str, list[dict[str, Any]]] = {
        shard_id: [] for shard_id in assignments_by_shard
    }
    seen: set[str] = set()
    environment = identity["environment_class_sha256"]
    for record in bundle.records:
        validate_record(record, run_hash)
        key = record["result_key"]
        if key in seen:
            raise ContractError("duplicate result record")
        seen.add(key)
        owner = assigned_owner.get(key)
        if owner is None or owner != record["shard_id"]:
            raise ContractError("unexpected or wrong-shard result record")
        if record["environment_class_sha256"] != environment:
            raise ContractError("measurement environment drift")
        by_shard[owner].append(record)

    if seen != set(assigned_owner):
        raise ContractError("missing assigned result records")

    if set(bundle.completions) != set(assignments_by_shard):
        raise ContractError("missing or unexpected shard completion")
    if set(bundle.attempts) != set(assignments_by_shard):
        raise ContractError("missing or unexpected shard attempts")

    for shard_id, assigned in assignments_by_shard.items():
        attempts = bundle.attempts[shard_id]
        for attempt in attempts:
            if set(attempt) != ATTEMPT_LAUNCH_FIELDS:
                raise ContractError("attempt launch field set mismatch")
            if attempt["run_identity_sha256"] != run_hash:
                raise ContractError("attempt run identity mismatch")
            if attempt["shard_id"] != shard_id:
                raise ContractError("attempt shard mismatch")
            if attempt["assigned_count"] != len(assigned):
                raise ContractError("attempt assigned count mismatch")
            if attempt["enforcement_id"] != run["resource_enforcement"]["enforcement_id"]:
                raise ContractError("attempt enforcement mismatch")
            if attempt["environment_class_sha256"] != environment:
                raise ContractError("attempt environment drift")
            terminal = attempt["terminal"]
            if terminal is not None and set(terminal) != ATTEMPT_TERMINAL_FIELDS:
                raise ContractError("attempt terminal field set mismatch")
            if terminal is not None and terminal["status"] == "completed":
                if terminal["exit_code"] != 0 or terminal["signal"] is not None:
                    raise ContractError("completed attempt exit mismatch")
                if terminal["completed_count"] != len(assigned):
                    raise ContractError("completed attempt count mismatch")
                if terminal["missing_result_keys"] != []:
                    raise ContractError("completed attempt declares missing results")
                if terminal["result_set_sha256"] != record_set_sha256(
                    by_shard[shard_id]
                ):
                    raise ContractError("completed attempt result-set hash mismatch")
        launch_ids = [attempt["attempt_id"] for attempt in attempts]
        if len(launch_ids) != len(set(launch_ids)) or not launch_ids:
            raise ContractError("invalid attempt identity set")
        naturally_unclosed = sorted(
            attempt["attempt_id"] for attempt in attempts if attempt.get("terminal") is None
        )
        completion = bundle.completions[shard_id]
        if set(completion) != SHARD_COMPLETION_FIELDS:
            raise ContractError("shard completion field set mismatch")
        if completion.get("state") != "complete":
            raise ContractError("non-complete shard")
        if completion.get("run_identity_sha256") != run_hash:
            raise ContractError("completion run identity mismatch")
        if sorted(completion.get("attempt_ids", [])) != sorted(launch_ids):
            raise ContractError("completion attempt accounting mismatch")
        if sorted(completion.get("unclosed_attempt_ids", [])) != naturally_unclosed:
            raise ContractError("unaccounted terminal-less attempt")
        rows = by_shard[shard_id]
        row_keys = {row["result_key"] for row in rows}
        if row_keys != assigned:
            raise ContractError("shard result population mismatch")
        if completion.get("assigned_count") != len(assigned):
            raise ContractError("completion assigned count mismatch")
        if completion.get("completed_count") != len(rows):
            raise ContractError("completion result count mismatch")
        if completion.get("missing_result_keys") != []:
            raise ContractError("complete shard declares missing results")
        if completion.get("result_set_sha256") != record_set_sha256(rows):
            raise ContractError("completion result-set hash mismatch")

    canonical_records = sorted(bundle.records, key=lambda row: row["result_key"])
    merged = {
        "schema": "axeyum.smtcomp-canonical-raw.v1",
        "run_identity_sha256": run_hash,
        "result_count": len(canonical_records),
        "records": canonical_records,
    }
    return canonical_bytes(merged)


def clone_bundle(bundle: Bundle) -> Bundle:
    return copy.deepcopy(bundle)
