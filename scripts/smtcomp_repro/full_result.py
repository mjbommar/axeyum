"""Completion-last external cell results for credited full execution.

The execution coordinator supplies a sealed authority that binds its final
wave, resource, and multi-host completions.  This module publishes only
process-free copies and summaries; it has no launch, SSH, or recovery path.
"""

from __future__ import annotations

import copy
import json
import time
from pathlib import Path
from typing import Any, Callable, Iterable

from full_compare import (
    summarize_full_cell_records,
    validate_full_cell_records,
)
from full_population import POPULATION_COUNT, SOLVER_IDS, WAVE_COUNT
from resume_contract import ContractError, canonical_bytes, digest
from resume_fs import atomic_install_bytes, atomic_install_json, read_canonical_json
from resume_runner import sha256_file


EXECUTION_AUTHORITY_SCHEMA = "axeyum.smtcomp-credited-full-cell-execution.v2"
ADJUDICATION_SCHEMA = "axeyum.smtcomp-credited-full-cell-adjudication.v2"
CELL_RESULT_SCHEMA = "axeyum.smtcomp-credited-full-cell-result.v1"
EXECUTION_AUTHORITY_FIELDS = {
    "schema",
    "fixture_only",
    "solver_id",
    "preparation_record_sha256",
    "selection_record_sha256",
    "run_identity_sha256",
    "plan_sha256",
    "schedule_record_sha256",
    "wave_checkpoint_record_sha256s",
    "resource_completion_record_sha256",
    "multi_host_completion_record_sha256",
    "prior_cell_result_record_sha256s",
    "cross_solver_disagreement_count",
    "population_count",
    "key_set_sha256",
    "record_set_sha256",
    "completed_at_ns",
    "record_sha256",
}
ADJUDICATION_FIELDS = {
    "schema",
    "solver_id",
    "execution_authority_record_sha256",
    "population_count",
    "key_set_sha256",
    "record_set_sha256",
    "summary",
    "known_status_contradictions",
    "cross_solver_disagreements",
    "safe_to_continue",
    "record_sha256",
}
CELL_RESULT_FIELDS = {
    "schema",
    "fixture_only",
    "solver_id",
    "preparation_record_sha256",
    "selection_record_sha256",
    "execution_authority_record_sha256",
    "execution_authority_file_sha256",
    "adjudication_record_sha256",
    "adjudication_file_sha256",
    "records_file_sha256",
    "population_count",
    "key_set_sha256",
    "record_set_sha256",
    "safe_to_continue",
    "published_at_ns",
    "record_sha256",
}
PhaseHook = Callable[[str], None]


def _expect(condition: bool, message: str) -> None:
    if not condition:
        raise ContractError(message)


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _is_sha256(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def build_full_execution_authority(
    *,
    solver_id: str,
    preparation_record_sha256: str,
    selection_record_sha256: str,
    run_identity_sha256: str,
    plan_sha256: str,
    schedule_record_sha256: str,
    wave_checkpoint_record_sha256s: list[str],
    resource_completion_record_sha256: str,
    multi_host_completion_record_sha256: str,
    prior_cell_result_record_sha256s: list[str],
    cross_solver_disagreement_count: int,
    population_count: int,
    key_set_sha256: str,
    record_set_sha256: str,
    completed_at_ns: int,
    fixture_only: bool = False,
) -> dict[str, Any]:
    """Build the immutable seam between supervised execution and publication."""

    record = _sealed(
        {
            "schema": EXECUTION_AUTHORITY_SCHEMA,
            "fixture_only": fixture_only,
            "solver_id": solver_id,
            "preparation_record_sha256": preparation_record_sha256,
            "selection_record_sha256": selection_record_sha256,
            "run_identity_sha256": run_identity_sha256,
            "plan_sha256": plan_sha256,
            "schedule_record_sha256": schedule_record_sha256,
            "wave_checkpoint_record_sha256s": copy.deepcopy(
                wave_checkpoint_record_sha256s
            ),
            "resource_completion_record_sha256": resource_completion_record_sha256,
            "multi_host_completion_record_sha256": multi_host_completion_record_sha256,
            "prior_cell_result_record_sha256s": copy.deepcopy(
                prior_cell_result_record_sha256s
            ),
            "cross_solver_disagreement_count": cross_solver_disagreement_count,
            "population_count": population_count,
            "key_set_sha256": key_set_sha256,
            "record_set_sha256": record_set_sha256,
            "completed_at_ns": completed_at_ns,
        }
    )
    return validate_full_execution_authority(record)


def validate_full_execution_authority(record: dict[str, Any]) -> dict[str, Any]:
    """Validate the exact final execution identities needed by a cell result."""

    _expect(
        isinstance(record, dict)
        and set(record) == EXECUTION_AUTHORITY_FIELDS
        and record.get("schema") == EXECUTION_AUTHORITY_SCHEMA
        and record.get("record_sha256") == _sealed(record)["record_sha256"],
        "full execution authority field/schema/seal mismatch",
    )
    fixture_only = record.get("fixture_only")
    _expect(type(fixture_only) is bool, "full execution authority fixture scope mismatch")
    _expect(
        record.get("solver_id") in SOLVER_IDS,
        "full execution authority solver identity mismatch",
    )
    for field in (
        "preparation_record_sha256",
        "selection_record_sha256",
        "run_identity_sha256",
        "plan_sha256",
        "schedule_record_sha256",
        "resource_completion_record_sha256",
        "multi_host_completion_record_sha256",
        "key_set_sha256",
        "record_set_sha256",
    ):
        _expect(_is_sha256(record.get(field)), "full execution authority hash mismatch")
    checkpoints = record.get("wave_checkpoint_record_sha256s")
    _expect(
        isinstance(checkpoints, list)
        and bool(checkpoints)
        and len(checkpoints) == len(set(checkpoints))
        and all(_is_sha256(value) for value in checkpoints),
        "full execution authority checkpoint inventory mismatch",
    )
    prior_results = record.get("prior_cell_result_record_sha256s")
    solver_index = SOLVER_IDS.index(record["solver_id"])
    _expect(
        isinstance(prior_results, list)
        and len(prior_results) == solver_index
        and len(prior_results) == len(set(prior_results))
        and all(_is_sha256(value) for value in prior_results),
        "full execution authority prior-cell inventory mismatch",
    )
    _expect(
        type(record.get("cross_solver_disagreement_count")) is int
        and record["cross_solver_disagreement_count"] >= 0
        and (
            solver_index > 0
            or record["cross_solver_disagreement_count"] == 0
        ),
        "full execution authority disagreement count mismatch",
    )
    population = record.get("population_count")
    _expect(
        type(population) is int
        and population > 0
        and type(record.get("completed_at_ns")) is int
        and record["completed_at_ns"] > 0,
        "full execution authority population/timestamp mismatch",
    )
    if not fixture_only:
        _expect(
            population == POPULATION_COUNT and len(checkpoints) == WAVE_COUNT,
            "live full execution authority differs from preregistration",
        )
    return record


def _records_bytes(records: Iterable[dict[str, Any]]) -> bytes:
    return b"".join(canonical_bytes(row) for row in sorted(records, key=lambda row: row["sequence"]))


def _load_records(path: Path) -> list[dict[str, Any]]:
    data = path.read_bytes()
    records = []
    for line in data.splitlines(keepends=True):
        try:
            record = json.loads(line)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ContractError("full cell result records are malformed") from exc
        if line != canonical_bytes(record):
            raise ContractError("full cell result record line is non-canonical")
        records.append(record)
    _expect(data == _records_bytes(records), "full cell result record order drift")
    return records


def load_full_cell_result(
    output_root: Path,
    *,
    expected_logic_counts: dict[str, int],
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Validate one external result and return its completion plus records."""

    completion = validate_full_cell_result(
        output_root, expected_logic_counts=expected_logic_counts
    )
    return completion, _load_records(output_root / "records.jsonl")


def _derive_adjudication(
    *,
    records: list[dict[str, Any]],
    execution_authority: dict[str, Any],
    expected_logic_counts: dict[str, int],
) -> dict[str, Any]:
    authority = validate_full_execution_authority(execution_authority)
    indexed = validate_full_cell_records(
        authority["solver_id"],
        records,
        expected_logic_counts=expected_logic_counts,
        fixture_only=authority["fixture_only"],
    )
    summary = summarize_full_cell_records(
        indexed, expected_logic_counts=expected_logic_counts
    )
    _expect(
        authority["population_count"] == summary["population"]
        and authority["key_set_sha256"] == summary["key_set_sha256"]
        and authority["record_set_sha256"] == summary["record_set_sha256"],
        "full cell result execution authority drift",
    )
    contradictions = summary["decision_expected_status_counts"][
        "known-contradiction"
    ]
    return _sealed(
        {
            "schema": ADJUDICATION_SCHEMA,
            "solver_id": authority["solver_id"],
            "execution_authority_record_sha256": authority["record_sha256"],
            "population_count": summary["population"],
            "key_set_sha256": summary["key_set_sha256"],
            "record_set_sha256": summary["record_set_sha256"],
            "summary": summary,
            "known_status_contradictions": contradictions,
            "cross_solver_disagreements": authority[
                "cross_solver_disagreement_count"
            ],
            "safe_to_continue": contradictions == 0
            and authority["cross_solver_disagreement_count"] == 0,
        }
    )


def validate_full_cell_adjudication(
    adjudication: dict[str, Any],
    *,
    records: list[dict[str, Any]],
    execution_authority: dict[str, Any],
    expected_logic_counts: dict[str, int],
) -> dict[str, Any]:
    """Replay a cell adjudication from its exact record set."""

    _expect(
        isinstance(adjudication, dict)
        and set(adjudication) == ADJUDICATION_FIELDS
        and adjudication.get("schema") == ADJUDICATION_SCHEMA
        and adjudication.get("record_sha256")
        == _sealed(adjudication)["record_sha256"],
        "full cell adjudication field/schema/seal mismatch",
    )
    expected = _derive_adjudication(
        records=records,
        execution_authority=execution_authority,
        expected_logic_counts=expected_logic_counts,
    )
    _expect(adjudication == expected, "full cell adjudication replay drift")
    return adjudication


def _validate_result_root(output_root: Path) -> Path:
    _expect(not output_root.is_symlink(), "full cell result root mismatch")
    root = output_root.resolve(strict=True)
    _expect(root.is_dir(), "full cell result root mismatch")
    names = {path.name for path in root.iterdir()}
    _expect(
        names
        == {
            "execution-authority.json",
            "cell-adjudication.json",
            "records.jsonl",
            "complete.json",
        },
        "full cell result publication inventory mismatch",
    )
    return root


def validate_full_cell_result(
    output_root: Path,
    *,
    expected_logic_counts: dict[str, int],
) -> dict[str, Any]:
    """Replay all bytes in one completion-last external cell result."""

    root = _validate_result_root(output_root)
    authority = validate_full_execution_authority(
        read_canonical_json(root / "execution-authority.json")
    )
    records = _load_records(root / "records.jsonl")
    adjudication = validate_full_cell_adjudication(
        read_canonical_json(root / "cell-adjudication.json"),
        records=records,
        execution_authority=authority,
        expected_logic_counts=expected_logic_counts,
    )
    completion = read_canonical_json(root / "complete.json")
    _expect(
        isinstance(completion, dict)
        and set(completion) == CELL_RESULT_FIELDS
        and completion.get("schema") == CELL_RESULT_SCHEMA
        and completion.get("record_sha256") == _sealed(completion)["record_sha256"],
        "full cell result completion field/schema/seal mismatch",
    )
    _expect(
        completion.get("solver_id") == authority["solver_id"]
        and completion.get("fixture_only") is authority["fixture_only"]
        and completion.get("preparation_record_sha256")
        == authority["preparation_record_sha256"]
        and completion.get("selection_record_sha256")
        == authority["selection_record_sha256"]
        and completion.get("execution_authority_record_sha256")
        == authority["record_sha256"]
        and completion.get("execution_authority_file_sha256")
        == sha256_file(root / "execution-authority.json")
        and completion.get("adjudication_record_sha256")
        == adjudication["record_sha256"]
        and completion.get("adjudication_file_sha256")
        == sha256_file(root / "cell-adjudication.json")
        and completion.get("records_file_sha256")
        == sha256_file(root / "records.jsonl")
        and completion.get("population_count") == adjudication["population_count"]
        and completion.get("key_set_sha256") == adjudication["key_set_sha256"]
        and completion.get("record_set_sha256") == adjudication["record_set_sha256"]
        and completion.get("safe_to_continue")
        is adjudication["safe_to_continue"]
        and type(completion.get("published_at_ns")) is int
        and completion["published_at_ns"] >= authority["completed_at_ns"],
        "full cell result completion drift",
    )
    return completion


def publish_full_cell_result(
    output_root: Path,
    *,
    records: Iterable[dict[str, Any]],
    execution_authority: dict[str, Any],
    expected_logic_counts: dict[str, int],
    published_at_ns: int | None = None,
    phase_hook: PhaseHook | None = None,
) -> dict[str, Any]:
    """Publish authority, records, adjudication, and ``complete.json`` last."""

    _expect(not output_root.is_symlink(), "full cell result root mismatch")
    root = output_root.resolve()
    if (root / "complete.json").exists():
        raise ContractError("full cell result is already complete")
    if root.exists():
        names = {path.name for path in root.iterdir()}
        _expect(
            names
            <= {
                "execution-authority.json",
                "cell-adjudication.json",
                "records.jsonl",
            },
            "full cell result prepublication inventory mismatch",
        )
    authority = validate_full_execution_authority(execution_authority)
    timestamp = time.time_ns() if published_at_ns is None else published_at_ns
    _expect(
        type(timestamp) is int and timestamp >= authority["completed_at_ns"],
        "full cell result publication timestamp mismatch",
    )
    material = list(records)
    adjudication = _derive_adjudication(
        records=material,
        execution_authority=authority,
        expected_logic_counts=expected_logic_counts,
    )
    atomic_install_json(root, "execution-authority.json", authority)
    if phase_hook is not None:
        phase_hook("after_execution_authority")
    atomic_install_bytes(root, "records.jsonl", _records_bytes(material))
    if phase_hook is not None:
        phase_hook("after_records")
    atomic_install_json(root, "cell-adjudication.json", adjudication)
    if phase_hook is not None:
        phase_hook("after_adjudication")
    completion = _sealed(
        {
            "schema": CELL_RESULT_SCHEMA,
            "fixture_only": authority["fixture_only"],
            "solver_id": authority["solver_id"],
            "preparation_record_sha256": authority["preparation_record_sha256"],
            "selection_record_sha256": authority["selection_record_sha256"],
            "execution_authority_record_sha256": authority["record_sha256"],
            "execution_authority_file_sha256": sha256_file(
                root / "execution-authority.json"
            ),
            "adjudication_record_sha256": adjudication["record_sha256"],
            "adjudication_file_sha256": sha256_file(root / "cell-adjudication.json"),
            "records_file_sha256": sha256_file(root / "records.jsonl"),
            "population_count": adjudication["population_count"],
            "key_set_sha256": adjudication["key_set_sha256"],
            "record_set_sha256": adjudication["record_set_sha256"],
            "safe_to_continue": adjudication["safe_to_continue"],
            "published_at_ns": timestamp,
        }
    )
    atomic_install_json(root, "complete.json", completion)
    if phase_hook is not None:
        phase_hook("after_completion")
    return validate_full_cell_result(
        root, expected_logic_counts=expected_logic_counts
    )


def comparison_authority_from_cell_results(
    cell_results: list[dict[str, Any]],
) -> dict[str, Any]:
    """Build the exact authority shape consumed by ``full_compare``."""

    _expect(
        isinstance(cell_results, list)
        and [row.get("solver_id") for row in cell_results] == list(SOLVER_IDS),
        "full comparison cell result order mismatch",
    )
    first = cell_results[0]
    population = first.get("population_count")
    for row in cell_results:
        _expect(
            isinstance(row, dict)
            and set(row) == CELL_RESULT_FIELDS
            and row.get("schema") == CELL_RESULT_SCHEMA
            and row.get("record_sha256") == _sealed(row)["record_sha256"]
            and row.get("preparation_record_sha256")
            == first.get("preparation_record_sha256")
            and row.get("selection_record_sha256")
            == first.get("selection_record_sha256")
            and row.get("fixture_only") is first.get("fixture_only")
            and row.get("population_count") == population
            and row.get("safe_to_continue") is True,
            "full comparison cell result authority mismatch",
        )
    return {
        "fixture_only": first["fixture_only"],
        "preparation_record_sha256": first["preparation_record_sha256"],
        "selection_record_sha256": first["selection_record_sha256"],
        "cell_results": [
            {
                "solver_id": row["solver_id"],
                "record_sha256": row["record_sha256"],
                "population_count": row["population_count"],
                "safe_to_continue": row["safe_to_continue"],
            }
            for row in cell_results
        ],
    }


def load_full_cell_results(
    result_roots: dict[str, Path],
    *,
    expected_logic_counts: dict[str, int],
) -> tuple[dict[str, Any], dict[str, list[dict[str, Any]]]]:
    """Validate three result roots and return comparison authority plus records."""

    _expect(
        tuple(result_roots) == SOLVER_IDS,
        "full comparison cell result root order mismatch",
    )
    completions = []
    records_by_solver = {}
    for solver_id in SOLVER_IDS:
        root = result_roots[solver_id]
        completion, records = load_full_cell_result(
            root, expected_logic_counts=expected_logic_counts
        )
        _expect(
            completion["solver_id"] == solver_id,
            "full comparison cell result root identity mismatch",
        )
        completions.append(completion)
        records_by_solver[solver_id] = records
    return comparison_authority_from_cell_results(completions), records_by_solver
