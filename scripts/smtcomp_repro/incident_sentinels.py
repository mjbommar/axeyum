"""Shared, fail-closed validation for SMT-COMP incident sentinels.

The repaired P0 runner produces these records.  The credited full-population
preflight consumes the same semantic boundary rather than trusting a copied
JSON list or a transitive run-manifest hash.
"""

from __future__ import annotations

import copy
import signal
from pathlib import Path
from typing import Any

from resume_contract import ContractError, digest
from resume_runner import sha256_file
from runner import parse_verdict


SENTINEL_SCHEMA = "axeyum.smtcomp-incident-sentinel.v2"
SOLVER_ENVIRONMENT = {
    "AYU_THREADS": "1",
    "OMP_NUM_THREADS": "1",
    "RAYON_NUM_THREADS": "1",
}
EXPECTED_SENTINELS = {
    "qf_abvfp": "6f0b87776052d1770e8503bcc593ad842cc649d533c41fa4a898808397524b8b",
    "qf_bvfp": "31ce580816bfb0647001f64ef480cdd779fe2f31da320354ea1ea63cd9da34ae",
    "qf_auflia": "dc7f8f51be688669321c8a9a15f2543fc070bc3a4c55b81c763604c34fa73bde",
}
SENTINEL_ROWS = (
    ("qf-abvfp-query-26", "qf_abvfp", "axeyum"),
    ("qf-abvfp-query-26", "qf_abvfp", "cvc5"),
    ("qf-abvfp-query-26", "qf_abvfp", "bitwuzla"),
    ("qf-bvfp-query-26", "qf_bvfp", "axeyum"),
    ("qf-bvfp-query-26", "qf_bvfp", "cvc5"),
    ("qf-bvfp-query-26", "qf_bvfp", "bitwuzla"),
    ("qf-auflia-pipeline-invalid", "qf_auflia", "axeyum"),
    ("qf-auflia-pipeline-invalid", "qf_auflia", "cvc5"),
)
SENTINEL_FIELDS = {
    "schema",
    "sentinel_id",
    "sentinel_kind",
    "sentinel_path",
    "sentinel_sha256",
    "solver_id",
    "solver_binary_sha256",
    "command_sha256",
    "environment_sha256",
    "observed_status",
    "termination_class",
    "exit_code",
    "signal",
    "resource_limit_kind",
    "started_at_ns",
    "ended_at_ns",
    "wall_time_ns",
    "runner_elapsed_ns",
    "stdout_path",
    "stdout_sha256",
    "stdout_bytes",
    "stderr_path",
    "stderr_sha256",
    "stderr_bytes",
    "record_sha256",
}


def seal_sentinel(value: dict[str, Any]) -> dict[str, Any]:
    """Return a deep-copied sentinel with its canonical record seal."""

    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _inside(path: Path, root: Path, label: str) -> Path:
    if not path.is_absolute() or path.is_symlink():
        raise ContractError(f"incident sentinel {label} path is not canonical")
    resolved = path.resolve(strict=True)
    if resolved != path:
        raise ContractError(f"incident sentinel {label} path is not canonical")
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise ContractError(f"incident sentinel {label} escapes attempt root") from exc
    if not resolved.is_file():
        raise ContractError(f"incident sentinel {label} path mismatch")
    return resolved


def _validate_termination(record: dict[str, Any]) -> None:
    termination = record.get("termination_class")
    exit_code = record.get("exit_code")
    terminating_signal = record.get("signal")
    resource = record.get("resource_limit_kind")
    if termination == "completed":
        valid = exit_code == 0 and terminating_signal is None and resource is None
    elif termination == "wall-timeout":
        valid = (
            exit_code is None
            and terminating_signal == signal.SIGKILL
            and resource == "wall"
        )
    else:
        valid = False
    if not valid:
        raise ContractError("incident sentinel termination is not safe")


def _record_path(record: dict[str, Any], field: str) -> Path:
    value = record.get(field)
    if not isinstance(value, str) or not value:
        raise ContractError("incident sentinel path field mismatch")
    return Path(value)


def validate_incident_sentinel_records(
    records: list[dict[str, Any]],
    *,
    attempt_root: Path,
    solver_binaries: dict[str, Path],
    fixture_only: bool = False,
) -> list[dict[str, Any]]:
    """Replay the exact eight-row incident matrix and its byte sidecars."""

    if type(fixture_only) is not bool:
        raise ContractError("incident sentinel fixture flag mismatch")
    if not isinstance(records, list) or len(records) != len(SENTINEL_ROWS):
        raise ContractError("incident sentinel row inventory mismatch")
    if set(solver_binaries) != {"axeyum", "cvc5", "bitwuzla"}:
        raise ContractError("incident sentinel binary inventory mismatch")
    attempt = attempt_root.resolve(strict=True)
    binaries = {
        solver_id: _inside(path, attempt, "binary")
        for solver_id, path in solver_binaries.items()
    }
    observed_rows = []
    previous_end = None
    for record, expected_row in zip(records, SENTINEL_ROWS, strict=True):
        if (
            not isinstance(record, dict)
            or set(record) != SENTINEL_FIELDS
            or record.get("schema") != SENTINEL_SCHEMA
            or record.get("record_sha256") != seal_sentinel(record)["record_sha256"]
        ):
            raise ContractError("incident sentinel field/schema/seal mismatch")
        sentinel_id, kind, solver_id = expected_row
        if (
            record.get("sentinel_id") != sentinel_id
            or record.get("sentinel_kind") != kind
            or record.get("solver_id") != solver_id
        ):
            raise ContractError("incident sentinel order/identity mismatch")
        sentinel_path = _inside(_record_path(record, "sentinel_path"), attempt, "input")
        stdout_path = _inside(_record_path(record, "stdout_path"), attempt, "stdout")
        stderr_path = _inside(_record_path(record, "stderr_path"), attempt, "stderr")
        binary = binaries[solver_id]
        command = [str(binary), str(sentinel_path)]
        if solver_id == "axeyum":
            command.extend(["--timeout-ms", "19000"])
        expected_hash = EXPECTED_SENTINELS[kind]
        stdout = stdout_path.read_bytes()
        stderr = stderr_path.read_bytes()
        observed = parse_verdict(stdout.decode("utf-8", errors="replace"))
        observed_status = observed.value if observed is not None else None
        if (
            record.get("sentinel_sha256") != sha256_file(sentinel_path)
            or (not fixture_only and record["sentinel_sha256"] != expected_hash)
            or record.get("solver_binary_sha256") != sha256_file(binary)
            or record.get("command_sha256") != digest(command)
            or record.get("environment_sha256") != digest(SOLVER_ENVIRONMENT)
            or record.get("observed_status") != observed_status
            or record.get("stdout_sha256") != sha256_file(stdout_path)
            or record.get("stdout_bytes") != len(stdout)
            or record.get("stderr_sha256") != sha256_file(stderr_path)
            or record.get("stderr_bytes") != len(stderr)
        ):
            raise ContractError("incident sentinel artifact identity drift")
        for field in ("started_at_ns", "ended_at_ns", "wall_time_ns", "runner_elapsed_ns"):
            if type(record.get(field)) is not int or record[field] < 0:
                raise ContractError("incident sentinel timestamp mismatch")
        if (
            record["started_at_ns"] <= 0
            or record["ended_at_ns"] < record["started_at_ns"]
            or (previous_end is not None and record["started_at_ns"] < previous_end)
        ):
            raise ContractError("incident sentinel observation interval mismatch")
        previous_end = record["ended_at_ns"]
        _validate_termination(record)
        completed = record["termination_class"] == "completed"
        if kind in {"qf_abvfp", "qf_bvfp"}:
            safe = completed and observed_status == "unsat"
        elif solver_id == "cvc5":
            safe = completed and observed_status == "sat"
        else:
            safe = (completed and observed_status in {"sat", "unknown"}) or (
                record["termination_class"] == "wall-timeout"
                and observed_status is None
            )
        if not safe:
            raise ContractError("incident sentinel outcome is unsafe")
        observed_rows.append(record)
    return observed_rows
