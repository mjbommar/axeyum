"""Executable v2 prototype for distributed SMT-COMP resume evidence.

V2 adds real-process attribution that v1 lacked: typed termination, separate
observed/admitted verdicts, attempt ownership, terminal result partitions, and
content-addressed output facts. It remains a planning prototype, not the
production remote runner.
"""

from __future__ import annotations

import copy
import hashlib
import json
import re
from dataclasses import dataclass
from typing import Any


CONTRACT_SCHEMA = "axeyum.smtcomp-resumable-run-contract.v2"
RUN_SCHEMA = "axeyum.smtcomp-run.v2"
RESULT_SCHEMA = "axeyum.smtcomp-result.v2"
CANONICAL_SCHEMA = "axeyum.smtcomp-canonical-scoring.v2"
VERDICT_POLICY = "smtcomp-2026-response-even-after-timeout"
HEX256 = re.compile(r"[0-9a-f]{64}\Z")

RUN_IDENTITY_FIELDS = {
    "contract_schema",
    "run_schema",
    "result_schema",
    "selection_manifest_sha256",
    "selected_list_sha256",
    "corpus_identity_sha256",
    "solver_id",
    "solver_binary_sha256",
    "solver_command_sha256",
    "solver_config_sha256",
    "runner_source_sha256",
    "repository_commit",
    "source_tree_state_sha256",
    "toolchain_identity_sha256",
    "track",
    "wall_limit_ms",
    "cpu_limit_ms",
    "memory_limit_bytes",
    "cores",
    "shard_count",
    "shard_mapping",
    "environment_class_sha256",
    "resource_policy_sha256",
    "output_capture_policy_sha256",
    "verdict_policy",
}
RESULT_RECORD_FIELDS = {
    "schema",
    "run_identity_sha256",
    "result_key",
    "benchmark_id",
    "benchmark_sha256",
    "solver_id",
    "solver_config_sha256",
    "shard_id",
    "sequence",
    "attempt_id",
    "environment_class_sha256",
    "expected_status",
    "observed_status",
    "reported_status",
    "verdict_admission",
    "termination_class",
    "exit_code",
    "signal",
    "resource_limit_kind",
    "wall_time_ns",
    "runner_elapsed_ns",
    "cpu_time_ns",
    "peak_rss_bytes",
    "stdout_sha256",
    "stdout_bytes",
    "stderr_sha256",
    "stderr_bytes",
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
    "durable_result_keys",
    "new_result_keys",
    "skipped_result_keys",
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


def result_key(
    benchmark_id: str, benchmark_sha256: str, solver_config_sha256: str
) -> str:
    return digest(
        {
            "benchmark_id": benchmark_id,
            "benchmark_sha256": benchmark_sha256,
            "solver_config_sha256": solver_config_sha256,
        }
    )


def seal_record(record: dict[str, Any]) -> dict[str, Any]:
    sealed = copy.deepcopy(record)
    sealed.pop("record_sha256", None)
    sealed["record_sha256"] = digest(sealed)
    return sealed


def _require_sha256(value: Any, field: str) -> None:
    if not isinstance(value, str) or not HEX256.fullmatch(value):
        raise ContractError(f"invalid SHA-256 field: {field}")


def _validate_termination(record: dict[str, Any]) -> None:
    kind = record["termination_class"]
    exit_code = record["exit_code"]
    signal = record["signal"]
    resource = record["resource_limit_kind"]
    if kind == "completed":
        valid = exit_code == 0 and signal is None and resource is None
    elif kind == "wall-timeout":
        valid = exit_code is None and isinstance(signal, int) and signal > 0 and resource == "wall"
    elif kind == "resource-limit":
        valid = (
            exit_code is None
            and (signal is None or isinstance(signal, int) and signal > 0)
            and resource in {"cpu", "memory"}
        )
    elif kind == "signal":
        valid = exit_code is None and isinstance(signal, int) and signal > 0 and resource is None
    elif kind == "nonzero-exit":
        valid = isinstance(exit_code, int) and exit_code != 0 and signal is None and resource is None
    elif kind == "runner-error":
        valid = exit_code is None and signal is None and resource is None
    else:
        valid = False
    if not valid:
        raise ContractError("illegal typed termination state")


def _validate_verdict(record: dict[str, Any]) -> None:
    valid_status = {None, "sat", "unsat", "unknown"}
    observed = record["observed_status"]
    reported = record["reported_status"]
    admission = record["verdict_admission"]
    if record["expected_status"] not in {None, "sat", "unsat"}:
        raise ContractError("invalid expected status")
    if observed not in valid_status or reported not in valid_status:
        raise ContractError("invalid verdict token")
    if observed is None:
        if reported is not None or admission != "no-verdict":
            raise ContractError("no-verdict admission mismatch")
    elif reported != observed or admission != "admitted":
        raise ContractError("observed verdict was not admitted")


def validate_record(
    record: dict[str, Any], run_identity_sha256: str, identity: dict[str, Any]
) -> None:
    if set(record) != RESULT_RECORD_FIELDS:
        raise ContractError("record field set mismatch")
    if record["schema"] != RESULT_SCHEMA:
        raise ContractError("record schema mismatch")
    if record["run_identity_sha256"] != run_identity_sha256:
        raise ContractError("record run identity mismatch")
    if record["solver_id"] != identity["solver_id"]:
        raise ContractError("record solver identity mismatch")
    if record["solver_config_sha256"] != identity["solver_config_sha256"]:
        raise ContractError("record solver configuration mismatch")
    expected_key = result_key(
        record["benchmark_id"],
        record["benchmark_sha256"],
        record["solver_config_sha256"],
    )
    if record["result_key"] != expected_key:
        raise ContractError("result key mismatch")
    for field in (
        "benchmark_sha256",
        "solver_config_sha256",
        "environment_class_sha256",
        "stdout_sha256",
        "stderr_sha256",
    ):
        _require_sha256(record[field], field)
    for field in (
        "sequence",
        "wall_time_ns",
        "runner_elapsed_ns",
        "cpu_time_ns",
        "peak_rss_bytes",
        "stdout_bytes",
        "stderr_bytes",
    ):
        if not isinstance(record[field], int) or record[field] < 0:
            raise ContractError(f"invalid nonnegative integer field: {field}")
    _validate_verdict(record)
    _validate_termination(record)
    wall_limit_ns = identity["wall_limit_ms"] * 1_000_000
    if record["wall_time_ns"] > wall_limit_ns:
        raise ContractError("scoring wall time exceeds registered limit")
    if record["runner_elapsed_ns"] < record["wall_time_ns"]:
        raise ContractError("runner elapsed time is below scoring wall time")
    if (
        record["termination_class"] == "wall-timeout"
        and record["wall_time_ns"] != wall_limit_ns
    ):
        raise ContractError("wall-timeout score is not clamped to limit")
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


def _measurement_projection(record: dict[str, Any]) -> dict[str, Any]:
    operational = {
        "attempt_id",
        "record_sha256",
        "stdout_sha256",
        "stdout_bytes",
        "stderr_sha256",
        "stderr_bytes",
    }
    return {key: value for key, value in record.items() if key not in operational}


def validate_run(run: dict[str, Any]) -> tuple[dict[str, Any], str]:
    """Validate the immutable run manifest before any solver is launched."""

    if run.get("schema") != RUN_SCHEMA:
        raise ContractError("run schema mismatch")
    identity = run.get("identity")
    if not isinstance(identity, dict) or run.get("identity_sha256") != digest(identity):
        raise ContractError("run identity mismatch")
    if set(identity) != RUN_IDENTITY_FIELDS:
        raise ContractError("run identity field set mismatch")
    if identity["contract_schema"] != CONTRACT_SCHEMA:
        raise ContractError("contract schema mismatch")
    if identity["run_schema"] != RUN_SCHEMA:
        raise ContractError("identity run schema mismatch")
    if identity["result_schema"] != RESULT_SCHEMA:
        raise ContractError("result schema mismatch")
    if identity["verdict_policy"] != VERDICT_POLICY:
        raise ContractError("unsupported verdict-admission policy")
    for field in RUN_IDENTITY_FIELDS:
        if field.endswith("_sha256"):
            _require_sha256(identity[field], field)
    expected_solver_config = digest(
        {
            "solver_id": identity["solver_id"],
            "solver_binary_sha256": identity["solver_binary_sha256"],
            "solver_command_sha256": identity["solver_command_sha256"],
        }
    )
    if identity["solver_config_sha256"] != expected_solver_config:
        raise ContractError("solver configuration digest mismatch")
    _validate_resources(run)
    return identity, run["identity_sha256"]


def merge_complete(bundle: Bundle) -> bytes:
    """Validate a complete evidence bundle and return canonical scoring bytes."""

    run = bundle.run
    identity, run_hash = validate_run(run)

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
        validate_record(record, run_hash, identity)
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
        rows = by_shard[shard_id]
        row_by_key = {row["result_key"]: row for row in rows}
        attempts = bundle.attempts[shard_id]
        attempt_by_id: dict[str, dict[str, Any]] = {}
        for attempt in attempts:
            if set(attempt) != ATTEMPT_LAUNCH_FIELDS:
                raise ContractError("attempt launch field set mismatch")
            attempt_id = attempt["attempt_id"]
            if attempt_id in attempt_by_id:
                raise ContractError("invalid attempt identity set")
            attempt_by_id[attempt_id] = attempt
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
            if terminal is None:
                continue
            if set(terminal) != ATTEMPT_TERMINAL_FIELDS:
                raise ContractError("attempt terminal field set mismatch")
            if terminal["status"] not in {
                "completed",
                "stopped",
                "failed",
                "cancelled",
                "resource-exhausted",
            }:
                raise ContractError("invalid attempt terminal status")
            durable = set(terminal["durable_result_keys"])
            new = set(terminal["new_result_keys"])
            skipped = set(terminal["skipped_result_keys"])
            missing = set(terminal["missing_result_keys"])
            if len(durable) != len(terminal["durable_result_keys"]):
                raise ContractError("duplicate durable terminal result")
            if new & skipped or new | skipped != durable:
                raise ContractError("terminal new/skipped partition mismatch")
            if durable | missing != assigned or durable & missing:
                raise ContractError("terminal durable/missing partition mismatch")
            if terminal["completed_count"] != len(durable):
                raise ContractError("terminal completed count mismatch")
            if terminal["result_set_sha256"] != record_set_sha256(
                [row_by_key[key] for key in durable]
            ):
                raise ContractError("terminal result-set hash mismatch")
            if any(row_by_key[key]["attempt_id"] != attempt_id for key in new):
                raise ContractError("terminal new-result attribution mismatch")
            if any(row_by_key[key]["attempt_id"] == attempt_id for key in skipped):
                raise ContractError("terminal skipped-result attribution mismatch")
            if terminal["status"] == "completed":
                if missing or terminal["exit_code"] != 0 or terminal["signal"] is not None:
                    raise ContractError("completed attempt terminal mismatch")

        if not attempt_by_id:
            raise ContractError("invalid attempt identity set")
        for row in rows:
            attempt = attempt_by_id.get(row["attempt_id"])
            if attempt is None:
                raise ContractError("record attempt attribution mismatch")
            terminal = attempt["terminal"]
            if terminal is not None and row["result_key"] not in terminal["new_result_keys"]:
                raise ContractError("closed-attempt record missing from new set")

        launch_ids = sorted(attempt_by_id)
        naturally_unclosed = sorted(
            attempt_id
            for attempt_id, attempt in attempt_by_id.items()
            if attempt["terminal"] is None
        )
        completion = bundle.completions[shard_id]
        if set(completion) != SHARD_COMPLETION_FIELDS:
            raise ContractError("shard completion field set mismatch")
        if completion.get("state") != "complete":
            raise ContractError("non-complete shard")
        if completion.get("run_identity_sha256") != run_hash:
            raise ContractError("completion run identity mismatch")
        if sorted(completion.get("attempt_ids", [])) != launch_ids:
            raise ContractError("completion attempt accounting mismatch")
        if sorted(completion.get("unclosed_attempt_ids", [])) != naturally_unclosed:
            raise ContractError("unaccounted terminal-less attempt")
        if set(row_by_key) != assigned:
            raise ContractError("shard result population mismatch")
        if completion.get("assigned_count") != len(assigned):
            raise ContractError("completion assigned count mismatch")
        if completion.get("completed_count") != len(rows):
            raise ContractError("completion result count mismatch")
        if completion.get("missing_result_keys") != []:
            raise ContractError("complete shard declares missing results")
        if completion.get("result_set_sha256") != record_set_sha256(rows):
            raise ContractError("completion result-set hash mismatch")

    canonical_records = sorted(
        (_measurement_projection(record) for record in bundle.records),
        key=lambda row: row["result_key"],
    )
    merged = {
        "schema": CANONICAL_SCHEMA,
        "run_identity_sha256": run_hash,
        "result_count": len(canonical_records),
        "records": canonical_records,
    }
    return canonical_bytes(merged)


def clone_bundle(bundle: Bundle) -> Bundle:
    return copy.deepcopy(bundle)
