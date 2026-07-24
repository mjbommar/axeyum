"""Fail-closed evidence replay for one completed credited-full solver cell.

This module is the process-free seam between supervised E1/E2/E3 execution
and external result publication.  It never launches, stops, probes, or recovers
a process.  Instead it replays the immutable F2 preparation, the complete wave
checkpoint chain, the underlying allocation/resource/multi-host evidence, all
v2 result records and output sidecars, and the safe prior-cell prefix before it
derives ``full_result`` execution authority.
"""

from __future__ import annotations

import copy
from collections import Counter
from pathlib import Path
from typing import Any

from full_compare import validate_full_cell_records
from full_execute import load_wave_checkpoints
from full_population import (
    CHECKPOINT_TERMINAL_FIELDS,
    POPULATION_COUNT,
    SOLVER_IDS,
    WAVE_COUNT,
    validate_checkpoint_chain,
    validate_schedule,
)
from full_prepare import validate_full_preparation
from full_result import (
    CELL_RESULT_FIELDS,
    CELL_RESULT_SCHEMA,
    build_full_execution_authority,
    load_full_cell_result,
    publish_full_cell_result,
)
from multi_host import (
    COMPLETION_FIELDS as MULTI_HOST_COMPLETION_FIELDS,
    COMPLETION_SCHEMA as MULTI_HOST_COMPLETION_SCHEMA,
    POST_RUN_COMPLETION_FIELDS,
    POST_RUN_COMPLETION_SCHEMA,
    TERMINAL_FIELDS as MULTI_HOST_TERMINAL_FIELDS,
    TERMINAL_SCHEMA as MULTI_HOST_TERMINAL_SCHEMA,
    validate_multi_host_state,
)
from resource_enforcement import (
    COMPLETION_FIELDS as RESOURCE_COMPLETION_FIELDS,
    COMPLETION_SCHEMA as RESOURCE_COMPLETION_SCHEMA,
    validate_resource_evidence,
)
from resume_contract import ContractError, digest, merge_complete
from resume_fs import load_bundle, read_canonical_json, verify_output_sidecars
from resume_runner import SELECTION_SCHEMA, sha256_bytes


SELECTION_FIELDS = {
    "schema",
    "run_identity_sha256",
    "selected_list_sha256",
    "benchmark_id_marker",
    "benchmarks",
}
SELECTION_ROW_FIELDS = {
    "sequence",
    "path",
    "benchmark_id",
    "benchmark_sha256",
    "input_bytes",
    "result_key",
    "logic",
    "expected_status",
    "num_named_assertions",
}


def _expect(condition: bool, message: str) -> None:
    if not condition:
        raise ContractError(message)


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _validate_sealed_record(
    record: dict[str, Any], *, fields: set[str], schema: str, label: str
) -> dict[str, Any]:
    _expect(
        isinstance(record, dict)
        and set(record) == fields
        and record.get("schema") == schema
        and record.get("record_sha256") == _sealed(record)["record_sha256"],
        f"{label} field/schema/seal mismatch",
    )
    return record


def _logic(benchmark_id: str) -> str:
    _expect("/" in benchmark_id, "full execution benchmark ID lacks logic")
    return benchmark_id.split("/", 1)[0]


def _validate_selection_records(
    selection: dict[str, Any],
    *,
    records: list[dict[str, Any]],
    run_identity_sha256: str,
    expected_logic_counts: dict[str, int],
) -> None:
    _expect(
        isinstance(selection, dict)
        and set(selection) == SELECTION_FIELDS
        and selection.get("schema") == SELECTION_SCHEMA
        and selection.get("run_identity_sha256") == run_identity_sha256,
        "full execution selection field/schema/identity mismatch",
    )
    rows = selection.get("benchmarks")
    _expect(isinstance(rows, list), "full execution selection rows mismatch")
    _expect(
        all(isinstance(row, dict) and set(row) == SELECTION_ROW_FIELDS for row in rows),
        "full execution selection row fields mismatch",
    )
    _expect(
        [row.get("sequence") for row in rows] == list(range(len(rows))),
        "full execution selection sequence mismatch",
    )
    by_key = {row.get("result_key"): row for row in rows}
    _expect(
        len(by_key) == len(rows) == len(records),
        "full execution selection/result population mismatch",
    )
    for record in records:
        row = by_key.get(record.get("result_key"))
        _expect(row is not None, "full execution result is outside selection")
        _expect(
            all(
                record.get(field) == row.get(field)
                for field in (
                    "sequence",
                    "benchmark_id",
                    "benchmark_sha256",
                    "expected_status",
                    "result_key",
                )
            ),
            "full execution result/selection identity drift",
        )
    observed_logics = dict(
        sorted(Counter(row["logic"] for row in rows).items())
    )
    _expect(
        observed_logics == dict(sorted(expected_logic_counts.items())),
        "full execution selection logic inventory drift",
    )
    _expect(
        all(row["logic"] == _logic(row["benchmark_id"]) for row in rows),
        "full execution selection logic/path drift",
    )


def _validate_completion_records(
    *,
    resource_completion: dict[str, Any],
    multi_host_completion: dict[str, Any],
    run_identity_sha256: str,
    plan_sha256: str,
    canonical_bundle_sha256: str,
) -> None:
    _validate_sealed_record(
        resource_completion,
        fields=RESOURCE_COMPLETION_FIELDS,
        schema=RESOURCE_COMPLETION_SCHEMA,
        label="full execution resource completion",
    )
    multi_schema = multi_host_completion.get("schema")
    if multi_schema == MULTI_HOST_COMPLETION_SCHEMA:
        multi_fields = MULTI_HOST_COMPLETION_FIELDS
    elif multi_schema == POST_RUN_COMPLETION_SCHEMA:
        multi_fields = POST_RUN_COMPLETION_FIELDS
    else:
        raise ContractError("full execution multi-host completion schema mismatch")
    _validate_sealed_record(
        multi_host_completion,
        fields=multi_fields,
        schema=multi_schema,
        label="full execution multi-host completion",
    )
    _expect(
        resource_completion.get("run_identity_sha256") == run_identity_sha256
        and multi_host_completion.get("run_identity_sha256")
        == run_identity_sha256
        and multi_host_completion.get("plan_sha256") == plan_sha256
        and multi_host_completion.get("resource_completion_sha256")
        == resource_completion["record_sha256"]
        and multi_host_completion.get("canonical_bundle_sha256")
        == canonical_bundle_sha256
        and type(resource_completion.get("completed_at_ns")) is int
        and type(multi_host_completion.get("completed_at_ns")) is int
        and multi_host_completion["completed_at_ns"]
        >= resource_completion["completed_at_ns"],
        "full execution completion identity/timestamp drift",
    )


def _validate_checkpoint_terminals(
    *,
    checkpoints: list[dict[str, Any]],
    terminal_evidence: list[dict[str, Any]],
) -> None:
    actual: dict[str, dict[str, Any]] = {}
    for terminal in terminal_evidence:
        _expect(
            isinstance(terminal, dict)
            and set(terminal) == CHECKPOINT_TERMINAL_FIELDS,
            "full execution terminal evidence fields mismatch",
        )
        record_sha256 = terminal.get("terminal_record_sha256")
        _expect(
            isinstance(record_sha256, str)
            and len(record_sha256) == 64
            and record_sha256 not in actual,
            "full execution terminal evidence identity mismatch",
        )
        actual[record_sha256] = terminal
    referenced: set[str] = set()
    for checkpoint in checkpoints:
        for shard in checkpoint["shard_completions"]:
            record_sha256 = shard["terminal_record_sha256"]
            terminal = actual.get(record_sha256)
            _expect(
                terminal is not None
                and terminal["allocation_id"] == shard["allocation_id"]
                and terminal["attempt_id"] == shard["attempt_id"]
                and terminal["status"] == shard["status"] == "completed",
                "full execution checkpoint lacks exact terminal evidence",
            )
            referenced.add(record_sha256)
    completed = {
        record_sha256
        for record_sha256, terminal in actual.items()
        if terminal["status"] == "completed"
    }
    _expect(
        completed == referenced,
        "full execution completed terminal/checkpoint accounting drift",
    )


def _validate_prior_cell_results(
    *,
    solver_id: str,
    prior_cell_results: list[tuple[dict[str, Any], list[dict[str, Any]]]],
    current_index: dict[tuple[str, str], dict[str, Any]],
    preparation_record_sha256: str,
    selection_record_sha256: str,
    expected_logic_counts: dict[str, int],
    fixture_only: bool,
) -> tuple[list[str], int]:
    solver_index = SOLVER_IDS.index(solver_id)
    _expect(
        isinstance(prior_cell_results, list)
        and len(prior_cell_results) == solver_index,
        "full execution prior-cell result count mismatch",
    )
    indexed = []
    result_hashes = []
    for expected_solver, material in zip(
        SOLVER_IDS[:solver_index], prior_cell_results, strict=True
    ):
        _expect(
            isinstance(material, tuple) and len(material) == 2,
            "full execution prior-cell result material mismatch",
        )
        completion, records = material
        _expect(
            isinstance(completion, dict)
            and set(completion) == CELL_RESULT_FIELDS
            and completion.get("schema") == CELL_RESULT_SCHEMA
            and completion.get("record_sha256")
            == _sealed(completion)["record_sha256"]
            and completion.get("solver_id") == expected_solver
            and completion.get("preparation_record_sha256")
            == preparation_record_sha256
            and completion.get("selection_record_sha256")
            == selection_record_sha256
            and completion.get("fixture_only") is fixture_only
            and completion.get("safe_to_continue") is True,
            "full execution prior-cell result authority mismatch",
        )
        prior_index = validate_full_cell_records(
            expected_solver,
            records,
            expected_logic_counts=expected_logic_counts,
            fixture_only=fixture_only,
        )
        _expect(
            set(prior_index) == set(current_index),
            "full execution prior/current population mismatch",
        )
        indexed.append(prior_index)
        result_hashes.append(completion["record_sha256"])
    disagreements = 0
    for key in current_index:
        decisions = {
            row[key]["reported_status"]
            for row in [*indexed, current_index]
            if row[key]["reported_status"] in {"sat", "unsat"}
        }
        disagreements += len(decisions) > 1
    return result_hashes, disagreements


def derive_full_execution_authority(
    *,
    solver_id: str,
    fixture_only: bool,
    preparation_record_sha256: str,
    selection_record_sha256: str,
    run_identity_sha256: str,
    plan_sha256: str,
    schedule: dict[str, Any],
    checkpoints: list[dict[str, Any]],
    records: list[dict[str, Any]],
    terminal_evidence: list[dict[str, Any]],
    resource_completion: dict[str, Any],
    multi_host_completion: dict[str, Any],
    canonical_bundle_sha256: str,
    expected_logic_counts: dict[str, int],
    prior_cell_results: list[tuple[dict[str, Any], list[dict[str, Any]]]],
) -> dict[str, Any]:
    """Derive publication authority only from a complete replayed cell."""

    _expect(solver_id in SOLVER_IDS, "full execution solver identity mismatch")
    _expect(type(fixture_only) is bool, "full execution fixture scope mismatch")
    validate_schedule(schedule)
    validate_checkpoint_chain(
        checkpoints,
        schedule=schedule,
        plan_sha256=plan_sha256,
        run_identity_sha256=run_identity_sha256,
        cell_id=solver_id,
    )
    _expect(
        len(checkpoints) == WAVE_COUNT
        and checkpoints[-1]["next_wave_index"] is None
        and checkpoints[-1]["cumulative_benchmark_count"] == POPULATION_COUNT,
        "full execution checkpoint chain is incomplete",
    )
    _validate_checkpoint_terminals(
        checkpoints=checkpoints, terminal_evidence=terminal_evidence
    )
    current_index = validate_full_cell_records(
        solver_id,
        records,
        expected_logic_counts=expected_logic_counts,
        fixture_only=fixture_only,
    )
    if not fixture_only:
        _expect(
            len(current_index) == POPULATION_COUNT,
            "live full execution population differs from preregistration",
        )
    key_set_sha256 = digest(
        [
            {"benchmark_id": key[0], "benchmark_sha256": key[1]}
            for key in sorted(current_index)
        ]
    )
    record_set_sha256 = digest(
        [
            {
                "benchmark_id": key[0],
                "benchmark_sha256": key[1],
                "record_sha256": current_index[key]["record_sha256"],
            }
            for key in sorted(current_index)
        ]
    )
    prior_hashes, disagreements = _validate_prior_cell_results(
        solver_id=solver_id,
        prior_cell_results=prior_cell_results,
        current_index=current_index,
        preparation_record_sha256=preparation_record_sha256,
        selection_record_sha256=selection_record_sha256,
        expected_logic_counts=expected_logic_counts,
        fixture_only=fixture_only,
    )
    _validate_completion_records(
        resource_completion=resource_completion,
        multi_host_completion=multi_host_completion,
        run_identity_sha256=run_identity_sha256,
        plan_sha256=plan_sha256,
        canonical_bundle_sha256=canonical_bundle_sha256,
    )
    return build_full_execution_authority(
        solver_id=solver_id,
        preparation_record_sha256=preparation_record_sha256,
        selection_record_sha256=selection_record_sha256,
        run_identity_sha256=run_identity_sha256,
        plan_sha256=plan_sha256,
        schedule_record_sha256=schedule["record_sha256"],
        wave_checkpoint_record_sha256s=[
            checkpoint["record_sha256"] for checkpoint in checkpoints
        ],
        resource_completion_record_sha256=resource_completion["record_sha256"],
        multi_host_completion_record_sha256=multi_host_completion[
            "record_sha256"
        ],
        prior_cell_result_record_sha256s=prior_hashes,
        cross_solver_disagreement_count=disagreements,
        population_count=len(current_index),
        key_set_sha256=key_set_sha256,
        record_set_sha256=record_set_sha256,
        completed_at_ns=multi_host_completion["completed_at_ns"],
        fixture_only=fixture_only,
    )


def _allocation_terminal_evidence(run_root: Path) -> list[dict[str, Any]]:
    root = run_root / "multi-host-terminals"
    _expect(root.is_dir() and not root.is_symlink(), "missing allocation terminals")
    evidence = []
    for allocation_root in sorted(root.iterdir(), key=lambda path: path.name):
        _expect(
            allocation_root.is_dir() and not allocation_root.is_symlink(),
            "unexpected allocation terminal namespace",
        )
        for path in sorted(allocation_root.iterdir(), key=lambda item: item.name):
            _expect(
                path.is_file() and not path.is_symlink() and path.suffix == ".json",
                "unexpected allocation terminal artifact",
            )
            terminal = read_canonical_json(path)
            _validate_sealed_record(
                terminal,
                fields=MULTI_HOST_TERMINAL_FIELDS,
                schema=MULTI_HOST_TERMINAL_SCHEMA,
                label="full execution allocation terminal",
            )
            _expect(
                path.stem == terminal.get("attempt_id"),
                "allocation terminal filename/attempt mismatch",
            )
            evidence.append(
                {
                    "allocation_id": allocation_root.name,
                    "attempt_id": terminal["attempt_id"],
                    "status": terminal["status"],
                    "terminal_record_sha256": terminal["record_sha256"],
                }
            )
    return evidence


def load_full_execution_authority(
    preparation_root: Path,
    *,
    repository_root: Path,
    solver_id: str,
    expected_logic_counts: dict[str, int],
    prior_result_roots: dict[str, Path],
    inspect_shared_root: bool = True,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Replay an on-disk cell and return derived authority plus v2 records."""

    _expect(solver_id in SOLVER_IDS, "full execution solver identity mismatch")
    solver_index = SOLVER_IDS.index(solver_id)
    _expect(
        tuple(prior_result_roots) == SOLVER_IDS[:solver_index],
        "full execution prior result root order mismatch",
    )
    allowed_prefix = SOLVER_IDS[: solver_index + 1]
    preparation = validate_full_preparation(
        preparation_root,
        repository_root=repository_root,
        inspect_shared_root=inspect_shared_root,
        allowed_execution_solver_ids=allowed_prefix,
    )
    attempt = preparation_root.resolve(strict=True)
    selection_preparation = read_canonical_json(
        attempt / "inputs" / "full-selection-preparation.json"
    )
    composition = read_canonical_json(
        attempt / "inputs" / "full-cell-composition.json"
    )
    cell = composition["cells"][solver_index]
    _expect(cell.get("solver_id") == solver_id, "full execution cell order drift")
    run_root = attempt / "cells" / solver_id
    run = read_canonical_json(Path(cell["run_manifest_path"]))
    plan = read_canonical_json(Path(cell["plan_path"]))
    schedule = validate_schedule(read_canonical_json(Path(cell["schedule_path"])))
    _expect(
        run_root.resolve(strict=True) == (attempt / "cells" / solver_id).resolve()
        and run.get("identity_sha256") == cell.get("run_identity_sha256")
        and plan.get("plan_sha256") == cell.get("plan_sha256")
        and schedule.get("record_sha256") == cell.get("schedule_record_sha256"),
        "full execution composition identity drift",
    )
    checkpoints = load_wave_checkpoints(
        run_root,
        schedule=schedule,
        plan_sha256=plan["plan_sha256"],
        run_identity_sha256=run["identity_sha256"],
        cell_id=solver_id,
    )
    bundle = load_bundle(run_root)
    verify_output_sidecars(run_root, bundle.records)
    validate_resource_evidence(run_root, bundle)
    multi_host_completion = validate_multi_host_state(
        run_root,
        bundle,
        require_completion=True,
        inspect_shared_root=inspect_shared_root,
    )
    canonical_bundle_sha256 = sha256_bytes(merge_complete(bundle))
    selection = read_canonical_json(run_root / "selection.json")
    _validate_selection_records(
        selection,
        records=bundle.records,
        run_identity_sha256=run["identity_sha256"],
        expected_logic_counts=expected_logic_counts,
    )
    resource_completion = read_canonical_json(
        run_root / "resource-completion.json"
    )
    prior_results = [
        load_full_cell_result(
            prior_result_roots[prior_solver],
            expected_logic_counts=expected_logic_counts,
        )
        for prior_solver in SOLVER_IDS[:solver_index]
    ]
    authority = derive_full_execution_authority(
        solver_id=solver_id,
        fixture_only=preparation["fixture_only"],
        preparation_record_sha256=preparation["record_sha256"],
        selection_record_sha256=selection_preparation["record_sha256"],
        run_identity_sha256=run["identity_sha256"],
        plan_sha256=plan["plan_sha256"],
        schedule=schedule,
        checkpoints=checkpoints,
        records=bundle.records,
        terminal_evidence=_allocation_terminal_evidence(run_root),
        resource_completion=resource_completion,
        multi_host_completion=multi_host_completion,
        canonical_bundle_sha256=canonical_bundle_sha256,
        expected_logic_counts=expected_logic_counts,
        prior_cell_results=prior_results,
    )
    return authority, bundle.records


def publish_full_cell_result_from_execution(
    preparation_root: Path,
    result_root: Path,
    *,
    repository_root: Path,
    solver_id: str,
    expected_logic_counts: dict[str, int],
    prior_result_roots: dict[str, Path],
    inspect_shared_root: bool = True,
    published_at_ns: int | None = None,
) -> dict[str, Any]:
    """Replay a complete cell, then publish its external result completion last."""

    authority, records = load_full_execution_authority(
        preparation_root,
        repository_root=repository_root,
        solver_id=solver_id,
        expected_logic_counts=expected_logic_counts,
        prior_result_roots=prior_result_roots,
        inspect_shared_root=inspect_shared_root,
    )
    return publish_full_cell_result(
        result_root,
        records=records,
        execution_authority=authority,
        expected_logic_counts=expected_logic_counts,
        published_at_ns=published_at_ns,
    )
