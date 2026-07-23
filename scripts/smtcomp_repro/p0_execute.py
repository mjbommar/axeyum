"""Single-cell coordinator for an integrated repaired-P0 preparation result."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Any, Callable

from multi_host import (
    finalize_multi_host_run,
    finish_allocation,
    start_allocation,
    validate_host_command,
)
from p0_prepare import validate_preparation
from resume_contract import ContractError, canonical_bytes, digest
from resume_fs import (
    atomic_install_bytes,
    atomic_install_json,
    read_canonical_json,
    validate_bundle_directory,
)
from resume_runner import legacy_raw_bytes, sha256_file


ADMISSION_PATH = Path(
    "docs/plan/smtcomp-repaired-p0-preparation-s1-result-2026-07-23.md"
)
CLOSURE_ADMISSION_PATH = Path(
    "docs/plan/smtcomp-repaired-p0-v2-export-layout-closure-plan-2026-07-23.md"
)
AXEYUM_CLOSURE_RESULT_PATH = Path(
    "docs/plan/smtcomp-repaired-p0-v2-axeyum-closure-result-2026-07-23.md"
)
CVC5_RESULT_PATH = Path(
    "docs/plan/smtcomp-repaired-p0-v2-cvc5-result-2026-07-23.md"
)
CELL_ORDER = ("axeyum", "cvc5", "bitwuzla")
ADJUDICATION_SCHEMA = "axeyum.smtcomp-repaired-p0-cell-adjudication.v1"
CELL_RESULT_SCHEMA = "axeyum.smtcomp-repaired-p0-cell-result.v1"
PhaseHook = Callable[[str], None]

FROZEN_AXEYUM_V2_CLOSURE = {
    "preparation_completion_sha256": "8d9145b2673ee10bf7c38990c20301f13323cfe4ab02c9946b403d0d2e4f4261",
    "run_identity_sha256": "5d75bf98f1fe7e8458ac1f5efbd75ea728bd57cff9b0c674002986c6e8dcd2d3",
    "record_count": 1810,
    "canonical_bundle_sha256": "104f27cd184b3aff00e33b2322409fcc707bf7f37f9c6a548e0bb6376f733c6a",
    "resource_completion_sha256": "99483e252237bf40afd99a556fc4b94a5b079dac36a032acd87a28bd55bcd900",
    "multi_host_completion_sha256": "8e2463fc157a6324149b2902739f7a282fec11c978b5ba467f6e529014c459cc",
    "adjudication_sha256": "fe880b9ae4dc04aeed938ad9e3fd7a350fe326cdba1a97fd6361721f85a6a824",
    "shard_completion_sha256s": {
        "0": "8fc09607434e042b280c6fc1b45259c6290345837ea6b72bf4ac1453c044f515",
        "1": "660396452b1e115d3311228e85ffa1be5cd8153db075801c708b4d7db000d6b5",
        "2": "d3fa627dfaf5d882709d46a0ecd30df310426b851aeef4b0d4b8839f91c4d718",
    },
    "allocation_terminal_sha256s": {
        "initial-0": "3901cc06a407575c01c234aced5084a17329d328189e985baed0f09beee77a95",
        "initial-1": "77d7774047ca83d735984d0d6707094536eff37b4cca728d6caa9e38fde8563d",
        "initial-2": "813fc263830e224f48d5d63c2e1635f60e6a626b5793141f572d9ad2a8a60909",
    },
}


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = dict(value)
    result["record_sha256"] = digest(result)
    return result


def require_integrated_path(repository_root: Path, relative: Path) -> None:
    """Require exact local bytes for ``relative`` to exist on origin/main."""

    local = repository_root / relative
    try:
        subprocess.check_output(
            ["git", "fetch", "--quiet", "origin", "main"],
            cwd=repository_root,
            stderr=subprocess.STDOUT,
        )
        integrated = subprocess.check_output(
            ["git", "show", f"origin/main:{relative.as_posix()}"],
            cwd=repository_root,
            stderr=subprocess.STDOUT,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ContractError(f"P0 admission is not integrated on origin/main: {relative}") from exc
    if integrated != local.read_bytes():
        raise ContractError(f"origin/main has different P0 admission bytes: {relative}")


def require_integrated_admission(repository_root: Path) -> None:
    """Require the exact local P0-S1 result bytes to exist on origin/main."""

    require_integrated_path(repository_root, ADMISSION_PATH)


def require_integrated_cell_admission(
    repository_root: Path, cell_id: str
) -> None:
    """Require every repository artifact that admits ``cell_id``."""

    if cell_id not in CELL_ORDER:
        raise ContractError("unknown repaired-P0 cell")
    require_integrated_admission(repository_root)
    require_integrated_path(repository_root, CLOSURE_ADMISSION_PATH)
    require_integrated_path(
        repository_root, Path("scripts/smtcomp_repro/p0_execute.py")
    )
    require_integrated_path(
        repository_root, Path("scripts/smtcomp_repro/resume_runner.py")
    )
    if cell_id != "axeyum":
        require_integrated_path(repository_root, AXEYUM_CLOSURE_RESULT_PATH)
    if cell_id == "bitwuzla":
        require_integrated_path(repository_root, CVC5_RESULT_PATH)


def _json_count(path: Path) -> int:
    return sum(1 for candidate in path.rglob("*.json") if candidate.is_file())


def _cell_by_id(completion: dict[str, Any]) -> dict[str, dict[str, Any]]:
    cells = {cell["solver_id"]: cell for cell in completion["cells"]}
    if tuple(cell["solver_id"] for cell in completion["cells"]) != CELL_ORDER:
        raise ContractError("P0 preparation cell order drift")
    return cells


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def cell_result_root(preparation_root: Path, cell_id: str) -> Path:
    """Return the coordinator-owned result namespace outside a cell run root."""

    if cell_id not in CELL_ORDER:
        raise ContractError("unknown repaired-P0 cell")
    return preparation_root / "cell-results" / cell_id


def _cell_result_material(
    *,
    preparation_root: Path,
    completion: dict[str, Any],
    cell_id: str,
    run_dir: Path,
    adjudication: dict[str, Any],
    raw_bytes: bytes,
) -> dict[str, Any]:
    multi_host = read_canonical_json(run_dir / "multi-host-completion.json")
    resource = read_canonical_json(run_dir / "resource-completion.json")
    canonical_bundle = validate_bundle_directory(
        run_dir, require_output_sidecars=True
    )
    raw = json.loads(raw_bytes)
    if not isinstance(raw, dict) or len(raw) != adjudication["record_count"]:
        raise ContractError("P0 raw export population mismatch")
    return {
        "schema": CELL_RESULT_SCHEMA,
        "solver_id": cell_id,
        "preparation_completion_sha256": sha256_file(
            preparation_root / "complete.json"
        ),
        "run_identity_sha256": adjudication["run_identity_sha256"],
        "canonical_bundle_sha256": _sha256_bytes(canonical_bundle),
        "resource_completion_sha256": sha256_file(
            run_dir / "resource-completion.json"
        ),
        "resource_completion_record_sha256": resource["record_sha256"],
        "multi_host_completion_sha256": sha256_file(
            run_dir / "multi-host-completion.json"
        ),
        "multi_host_completion_record_sha256": multi_host["record_sha256"],
        "adjudication_sha256": _sha256_bytes(canonical_bytes(adjudication)),
        "adjudication_record_sha256": adjudication["record_sha256"],
        "raw_results_sha256": _sha256_bytes(raw_bytes),
        "raw_result_count": len(raw),
        "safe_to_continue": adjudication["safe_to_continue"],
        "preparation_record_sha256": completion["record_sha256"],
    }


def validate_cell_result(
    *,
    preparation_root: Path,
    completion: dict[str, Any],
    cell_id: str,
    run_dir: Path,
) -> dict[str, Any]:
    """Validate completion-last coordinator outputs outside the run root."""

    result_root = cell_result_root(preparation_root, cell_id)
    if not result_root.is_dir():
        raise ContractError(f"missing P0 cell result: {cell_id}")
    allowed = {"p0-cell-adjudication.json", "raw-results.json", "complete.json"}
    unexpected = sorted(path.name for path in result_root.iterdir() if path.name not in allowed)
    if unexpected:
        raise ContractError(f"unexpected P0 cell-result artifact: {unexpected[0]}")
    if set(path.name for path in result_root.iterdir()) != allowed:
        raise ContractError(f"incomplete P0 cell result: {cell_id}")
    adjudication = read_canonical_json(result_root / "p0-cell-adjudication.json")
    expected_adjudication = adjudicate_cell(
        completion=completion,
        cell_id=cell_id,
        run_dir=run_dir,
    )
    if adjudication != expected_adjudication:
        raise ContractError(f"P0 cell adjudication drift: {cell_id}")
    raw_bytes = (result_root / "raw-results.json").read_bytes()
    if raw_bytes != legacy_raw_bytes(run_dir):
        raise ContractError(f"P0 raw export drift: {cell_id}")
    observed = read_canonical_json(result_root / "complete.json")
    unsealed = dict(observed)
    claimed = unsealed.pop("record_sha256", None)
    if claimed != digest(unsealed):
        raise ContractError(f"P0 cell-result completion hash mismatch: {cell_id}")
    expected = _sealed(
        _cell_result_material(
            preparation_root=preparation_root,
            completion=completion,
            cell_id=cell_id,
            run_dir=run_dir,
            adjudication=adjudication,
            raw_bytes=raw_bytes,
        )
    )
    if observed != expected:
        raise ContractError(f"P0 cell-result completion drift: {cell_id}")
    return observed


def validate_cell_launch(
    *,
    repository_root: Path,
    preparation_root: Path,
    cell_id: str,
    acknowledged_completion_sha256: str,
    require_integrated: bool = True,
) -> tuple[dict[str, Any], dict[str, Any], Path, dict[str, Path]]:
    """Validate the exact next cell without publishing an attempt."""

    if cell_id not in CELL_ORDER:
        raise ContractError("unknown repaired-P0 cell")
    if require_integrated:
        require_integrated_cell_admission(repository_root, cell_id)
    complete_path = preparation_root / "complete.json"
    if sha256_file(complete_path) != acknowledged_completion_sha256:
        raise ContractError("operator acknowledgement names another preparation")
    completion = validate_preparation(preparation_root, require_empty=False)
    cells = _cell_by_id(completion)
    active_index = CELL_ORDER.index(cell_id)

    for prior_id in CELL_ORDER[:active_index]:
        prior_root = Path(cells[prior_id]["attempt_root"])
        if not (prior_root / "multi-host-completion.json").is_file():
            raise ContractError(f"prior P0 cell is incomplete: {prior_id}")
        finalize_multi_host_run(prior_root)
        result = validate_cell_result(
            preparation_root=preparation_root,
            completion=completion,
            cell_id=prior_id,
            run_dir=prior_root,
        )
        if result.get("safe_to_continue") is not True:
            raise ContractError(f"prior P0 cell blocks continuation: {prior_id}")
    for later_id in CELL_ORDER[active_index + 1 :]:
        later_root = Path(cells[later_id]["attempt_root"])
        if _json_count(later_root / "multi-host-attempts"):
            raise ContractError(f"later P0 cell was attempted out of order: {later_id}")

    cell = cells[cell_id]
    run_dir = Path(cell["attempt_root"])
    if (run_dir / "multi-host-completion.json").exists():
        raise ContractError("P0 cell is already complete")
    for relative in (
        "multi-host-attempts",
        "multi-host-terminals",
        "resource-sessions",
        "attempts",
        "terminals",
        "records",
    ):
        if _json_count(run_dir / relative):
            raise ContractError("P0 cell contains prior execution evidence")

    plan = read_canonical_json(run_dir / "multi-host-plan.json")
    run_path = Path(cell["run_manifest_path"])
    try:
        run_path.resolve(strict=True).relative_to(preparation_root / "inputs")
    except ValueError as exc:
        raise ContractError("P0 cell run manifest escapes the input namespace") from exc
    run = read_canonical_json(run_path)
    if (
        run["identity_sha256"] != cell["run_identity_sha256"]
        or sha256_file(run_path) != cell["run_manifest_sha256"]
        or plan["plan_sha256"] != cell["plan_sha256"]
    ):
        raise ContractError("P0 cell run/plan identity drift")
    commands = {}
    for allocation_id in ("initial-0", "initial-1", "initial-2"):
        path = run_dir / "multi-host-commands" / f"{allocation_id}.json"
        command = read_canonical_json(path)
        if command.get("run_manifest_path") != str(run_path):
            raise ContractError("P0 command run-manifest path drift")
        command_plan, command_run, allocation = validate_host_command(command)
        if (
            command_plan["plan_sha256"] != plan["plan_sha256"]
            or command_run["identity_sha256"] != run["identity_sha256"]
            or allocation["generation"] != 0
        ):
            raise ContractError("P0 initial command identity drift")
        commands[allocation_id] = path
    return completion, plan, run_dir, commands


def _records(run_dir: Path) -> list[dict[str, Any]]:
    rows = []
    for path in sorted((run_dir / "records").glob("*.json")):
        row = read_canonical_json(path)
        if path.name != f"{row.get('result_key')}.json":
            raise ContractError("P0 result filename/key mismatch")
        rows.append(row)
    return rows


def adjudicate_cell(
    *,
    completion: dict[str, Any],
    cell_id: str,
    run_dir: Path,
) -> dict[str, Any]:
    """Reject known-status contradictions and completed-cell disagreements."""

    cells = _cell_by_id(completion)
    records = _records(run_dir)
    contradictions = []
    disagreements = []
    prior_decisions: dict[tuple[str, str], tuple[str, str]] = {}
    for prior_id in CELL_ORDER[: CELL_ORDER.index(cell_id)]:
        prior_root = Path(cells[prior_id]["attempt_root"])
        for row in _records(prior_root):
            status = row["reported_status"]
            if status in {"sat", "unsat"}:
                prior_decisions[(row["benchmark_id"], row["benchmark_sha256"])] = (
                    prior_id,
                    status,
                )
    for row in records:
        expected = row["expected_status"]
        observed = row["reported_status"]
        if expected in {"sat", "unsat"} and observed in {"sat", "unsat"} and expected != observed:
            contradictions.append(
                {
                    "benchmark_id": row["benchmark_id"],
                    "benchmark_sha256": row["benchmark_sha256"],
                    "expected_status": expected,
                    "observed_status": observed,
                }
            )
        previous = prior_decisions.get((row["benchmark_id"], row["benchmark_sha256"]))
        if previous is not None and observed in {"sat", "unsat"} and previous[1] != observed:
            disagreements.append(
                {
                    "benchmark_id": row["benchmark_id"],
                    "benchmark_sha256": row["benchmark_sha256"],
                    "prior_solver": previous[0],
                    "prior_status": previous[1],
                    "solver": cell_id,
                    "status": observed,
                }
            )
    status_counts = Counter(row["reported_status"] or "no-verdict" for row in records)
    termination_counts = Counter(row["termination_class"] for row in records)
    return _sealed(
        {
            "schema": ADJUDICATION_SCHEMA,
            "solver_id": cell_id,
            "run_identity_sha256": read_canonical_json(
                Path(_cell_by_id(completion)[cell_id]["run_manifest_path"])
            )["identity_sha256"],
            "record_count": len(records),
            "status_counts": dict(sorted(status_counts.items())),
            "termination_counts": dict(sorted(termination_counts.items())),
            "known_status_contradictions": contradictions,
            "cross_solver_disagreements": disagreements,
            "safe_to_continue": not contradictions and not disagreements,
        }
    )


def validate_cell_adjudication(
    *,
    completion: dict[str, Any],
    cell_id: str,
    run_dir: Path,
    adjudication_path: Path,
) -> dict[str, Any]:
    observed = read_canonical_json(adjudication_path)
    expected = adjudicate_cell(
        completion=completion,
        cell_id=cell_id,
        run_dir=run_dir,
    )
    if observed != expected:
        raise ContractError(f"P0 cell adjudication drift: {cell_id}")
    return observed


def _require_file_hash(path: Path, expected: str, label: str) -> None:
    if not path.is_file() or sha256_file(path) != expected:
        raise ContractError(f"frozen P0 closure hash mismatch: {label}")


def _legacy_quarantine_path(run_dir: Path, adjudication_sha256: str) -> Path:
    return (
        run_dir
        / "quarantine"
        / f"p0-cell-adjudication-layout-v1-{adjudication_sha256}.json"
    )


def _frozen_legacy_adjudication(
    run_dir: Path, frozen: dict[str, Any]
) -> tuple[bytes, Path, Path]:
    source = run_dir / "p0-cell-adjudication.json"
    destination = _legacy_quarantine_path(
        run_dir, frozen["adjudication_sha256"]
    )
    present = [path for path in (source, destination) if path.is_file()]
    if len(present) != 1:
        raise ContractError("frozen P0 closure adjudication location mismatch")
    data = present[0].read_bytes()
    if _sha256_bytes(data) != frozen["adjudication_sha256"]:
        raise ContractError("frozen P0 closure adjudication hash mismatch")
    return data, source, destination


def validate_frozen_axeyum_v2_closure(
    *, preparation_root: Path, completion: dict[str, Any], run_dir: Path
) -> bytes:
    """Validate the exact completed Axeyum v2 stop state before migration."""

    frozen = FROZEN_AXEYUM_V2_CLOSURE
    _require_file_hash(
        preparation_root / "complete.json",
        frozen["preparation_completion_sha256"],
        "preparation completion",
    )
    cell = _cell_by_id(completion)["axeyum"]
    if cell["run_identity_sha256"] != frozen["run_identity_sha256"]:
        raise ContractError("frozen P0 closure run identity mismatch")
    if len(_records(run_dir)) != frozen["record_count"]:
        raise ContractError("frozen P0 closure record count mismatch")
    _require_file_hash(
        run_dir / "resource-completion.json",
        frozen["resource_completion_sha256"],
        "resource completion",
    )
    _require_file_hash(
        run_dir / "multi-host-completion.json",
        frozen["multi_host_completion_sha256"],
        "multi-host completion",
    )
    for shard_id, expected in frozen["shard_completion_sha256s"].items():
        _require_file_hash(
            run_dir / "completions" / f"{shard_id}.json",
            expected,
            f"shard {shard_id} completion",
        )
    for allocation_id, expected in frozen["allocation_terminal_sha256s"].items():
        paths = sorted((run_dir / "multi-host-terminals" / allocation_id).glob("*.json"))
        if len(paths) != 1:
            raise ContractError(
                f"frozen P0 closure allocation terminal mismatch: {allocation_id}"
            )
        _require_file_hash(paths[0], expected, f"allocation {allocation_id} terminal")
    data, _source, _destination = _frozen_legacy_adjudication(run_dir, frozen)
    expected_adjudication = adjudicate_cell(
        completion=completion,
        cell_id="axeyum",
        run_dir=run_dir,
    )
    if data != canonical_bytes(expected_adjudication):
        raise ContractError("frozen P0 closure adjudication content mismatch")
    return data


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def migrate_legacy_adjudication(
    *,
    run_dir: Path,
    adjudication_sha256: str,
    phase_hook: PhaseHook | None = None,
) -> None:
    """Move only the exact legacy coordinator artifact into quarantine."""

    source = run_dir / "p0-cell-adjudication.json"
    destination = _legacy_quarantine_path(run_dir, adjudication_sha256)
    if destination.exists():
        if not destination.is_file() or sha256_file(destination) != adjudication_sha256:
            raise ContractError("frozen P0 closure quarantine conflict")
        if source.exists():
            raise ContractError("frozen P0 closure duplicate adjudication")
        return
    if not source.is_file() or sha256_file(source) != adjudication_sha256:
        raise ContractError("frozen P0 closure source adjudication mismatch")
    destination.parent.mkdir(parents=True, exist_ok=True)
    os.replace(source, destination)
    _fsync_directory(destination.parent)
    _fsync_directory(run_dir)
    if phase_hook:
        phase_hook("after_legacy_quarantine")


def publish_cell_result(
    *,
    preparation_root: Path,
    completion: dict[str, Any],
    cell_id: str,
    run_dir: Path,
    legacy_adjudication: bytes | None = None,
    phase_hook: PhaseHook | None = None,
) -> dict[str, Any]:
    """Publish adjudication, raw export, and completion outside the run root."""

    adjudication = adjudicate_cell(
        completion=completion,
        cell_id=cell_id,
        run_dir=run_dir,
    )
    adjudication_bytes = canonical_bytes(adjudication)
    if legacy_adjudication is not None and legacy_adjudication != adjudication_bytes:
        raise ContractError("legacy P0 adjudication differs from recomputation")
    result_root = cell_result_root(preparation_root, cell_id)
    atomic_install_bytes(
        result_root,
        "p0-cell-adjudication.json",
        adjudication_bytes,
        quarantine_root=result_root / "quarantine",
    )
    if phase_hook:
        phase_hook("after_external_adjudication")
    if legacy_adjudication is not None:
        migrate_legacy_adjudication(
            run_dir=run_dir,
            adjudication_sha256=_sha256_bytes(legacy_adjudication),
            phase_hook=phase_hook,
        )
    finalize_multi_host_run(run_dir)
    raw_bytes = legacy_raw_bytes(run_dir)
    atomic_install_bytes(
        result_root,
        "raw-results.json",
        raw_bytes,
        quarantine_root=result_root / "quarantine",
    )
    if phase_hook:
        phase_hook("after_raw_export")
    result = _sealed(
        _cell_result_material(
            preparation_root=preparation_root,
            completion=completion,
            cell_id=cell_id,
            run_dir=run_dir,
            adjudication=adjudication,
            raw_bytes=raw_bytes,
        )
    )
    atomic_install_json(
        result_root,
        "complete.json",
        result,
        quarantine_root=result_root / "quarantine",
    )
    if phase_hook:
        phase_hook("after_cell_result_completion")
    return validate_cell_result(
        preparation_root=preparation_root,
        completion=completion,
        cell_id=cell_id,
        run_dir=run_dir,
    )


def close_frozen_axeyum_v2(
    *,
    repository_root: Path,
    preparation_root: Path,
    acknowledged_completion_sha256: str,
    require_integrated: bool = True,
    phase_hook: PhaseHook | None = None,
) -> dict[str, Any]:
    """Close the exact completed Axeyum v2 cell without launching a process."""

    if require_integrated:
        require_integrated_admission(repository_root)
        require_integrated_path(repository_root, CLOSURE_ADMISSION_PATH)
        require_integrated_path(
            repository_root, Path("scripts/smtcomp_repro/p0_execute.py")
        )
        require_integrated_path(
            repository_root, Path("scripts/smtcomp_repro/resume_runner.py")
        )
    complete_path = preparation_root / "complete.json"
    if sha256_file(complete_path) != acknowledged_completion_sha256:
        raise ContractError("operator acknowledgement names another preparation")
    completion = validate_preparation(preparation_root, require_empty=False)
    run_dir = Path(_cell_by_id(completion)["axeyum"]["attempt_root"])
    legacy = validate_frozen_axeyum_v2_closure(
        preparation_root=preparation_root,
        completion=completion,
        run_dir=run_dir,
    )
    result = publish_cell_result(
        preparation_root=preparation_root,
        completion=completion,
        cell_id="axeyum",
        run_dir=run_dir,
        legacy_adjudication=legacy,
        phase_hook=phase_hook,
    )
    if result["canonical_bundle_sha256"] != FROZEN_AXEYUM_V2_CLOSURE[
        "canonical_bundle_sha256"
    ]:
        raise ContractError("frozen P0 closure canonical bundle mismatch")
    return result


def execute_cell(
    *,
    repository_root: Path,
    preparation_root: Path,
    cell_id: str,
    acknowledged_completion_sha256: str,
    poll_seconds: float = 30.0,
) -> dict[str, Any]:
    completion, plan, run_dir, commands = validate_cell_launch(
        repository_root=repository_root,
        preparation_root=preparation_root,
        cell_id=cell_id,
        acknowledged_completion_sha256=acknowledged_completion_sha256,
    )
    handles = {}
    start_error = None
    try:
        for allocation_id in sorted(commands):
            handles[allocation_id] = start_allocation(
                plan=plan,
                command_manifest=commands[allocation_id],
                run_dir=run_dir,
            )
            print(
                f"P0_CELL_STARTED|cell={cell_id}|allocation={allocation_id}",
                flush=True,
            )
    except (ContractError, OSError) as exc:
        start_error = exc

    pending = dict(handles)
    terminals = {}
    while pending:
        for allocation_id, handle in list(pending.items()):
            if handle.process.poll() is not None:
                terminals[allocation_id] = finish_allocation(handle, timeout=1.0)
                del pending[allocation_id]
                print(
                    f"P0_CELL_TERMINAL|cell={cell_id}|allocation={allocation_id}|"
                    f"status={terminals[allocation_id]['status']}",
                    flush=True,
                )
        if pending:
            print(
                f"P0_CELL_PROGRESS|cell={cell_id}|pending={','.join(sorted(pending))}|"
                f"records={len(_records(run_dir))}",
                flush=True,
            )
            time.sleep(poll_seconds)
    if start_error is not None:
        raise ContractError(
            "P0 cell only partially started; completed partial evidence retained"
        ) from start_error
    if {row["status"] for row in terminals.values()} != {"completed"}:
        raise ContractError("P0 cell has a failed/lost allocation; exact recovery required")

    finalize_multi_host_run(run_dir)
    publish_cell_result(
        preparation_root=preparation_root,
        completion=completion,
        cell_id=cell_id,
        run_dir=run_dir,
    )
    return validate_cell_adjudication(
        completion=completion,
        cell_id=cell_id,
        run_dir=run_dir,
        adjudication_path=cell_result_root(preparation_root, cell_id)
        / "p0-cell-adjudication.json",
    )


def main() -> int:
    repository_root = Path(__file__).resolve().parents[2]
    ap = argparse.ArgumentParser(description="execute one integrated repaired-P0 cell")
    ap.add_argument("--preparation-root", required=True, type=Path)
    ap.add_argument("--cell", required=True, choices=CELL_ORDER)
    ap.add_argument("--acknowledge-complete-sha256", required=True)
    ap.add_argument("--poll-seconds", type=float, default=30.0)
    ap.add_argument(
        "--close-completed",
        action="store_true",
        help="perform the preregistered process-free Axeyum v2 closure",
    )
    args = ap.parse_args()
    if len(args.acknowledge_complete_sha256) != 64:
        ap.error("--acknowledge-complete-sha256 must be a SHA-256")
    if not 1.0 <= args.poll_seconds <= 60.0:
        ap.error("--poll-seconds must be between 1 and 60")
    if args.close_completed and args.cell != "axeyum":
        ap.error("--close-completed is restricted to the frozen Axeyum v2 cell")
    try:
        preparation_root = args.preparation_root.resolve(strict=True)
        if args.close_completed:
            adjudication = close_frozen_axeyum_v2(
                repository_root=repository_root,
                preparation_root=preparation_root,
                acknowledged_completion_sha256=args.acknowledge_complete_sha256,
            )
        else:
            adjudication = execute_cell(
                repository_root=repository_root,
                preparation_root=preparation_root,
                cell_id=args.cell,
                acknowledged_completion_sha256=args.acknowledge_complete_sha256,
                poll_seconds=args.poll_seconds,
            )
    except (ContractError, OSError, subprocess.CalledProcessError) as exc:
        print(f"P0 cell rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(adjudication, sort_keys=True, separators=(",", ":")))
    return 0 if adjudication["safe_to_continue"] else 4


if __name__ == "__main__":
    raise SystemExit(main())
