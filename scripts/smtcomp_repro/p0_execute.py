"""Single-cell coordinator for an integrated repaired-P0 preparation result."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Any

from multi_host import (
    finalize_multi_host_run,
    finish_allocation,
    start_allocation,
    validate_host_command,
)
from p0_prepare import validate_preparation
from resume_contract import ContractError, digest
from resume_fs import atomic_install_json, read_canonical_json
from resume_runner import export_legacy_raw, sha256_file


ADMISSION_PATH = Path(
    "docs/plan/smtcomp-repaired-p0-preparation-s1-result-2026-07-23.md"
)
CELL_ORDER = ("axeyum", "cvc5", "bitwuzla")
ADJUDICATION_SCHEMA = "axeyum.smtcomp-repaired-p0-cell-adjudication.v1"


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = dict(value)
    result["record_sha256"] = digest(result)
    return result


def require_integrated_admission(repository_root: Path) -> None:
    """Require the exact local P0-S1 result bytes to exist on origin/main."""

    local = repository_root / ADMISSION_PATH
    try:
        subprocess.check_output(
            ["git", "fetch", "--quiet", "origin", "main"],
            cwd=repository_root,
            stderr=subprocess.STDOUT,
        )
        integrated = subprocess.check_output(
            ["git", "show", f"origin/main:{ADMISSION_PATH.as_posix()}"],
            cwd=repository_root,
            stderr=subprocess.STDOUT,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ContractError("P0-S1 result is not integrated on origin/main") from exc
    if integrated != local.read_bytes():
        raise ContractError("origin/main has different P0-S1 admission bytes")


def _json_count(path: Path) -> int:
    return sum(1 for candidate in path.rglob("*.json") if candidate.is_file())


def _cell_by_id(completion: dict[str, Any]) -> dict[str, dict[str, Any]]:
    cells = {cell["solver_id"]: cell for cell in completion["cells"]}
    if tuple(cell["solver_id"] for cell in completion["cells"]) != CELL_ORDER:
        raise ContractError("P0 preparation cell order drift")
    return cells


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
        require_integrated_admission(repository_root)
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
        adjudication = validate_cell_adjudication(
            completion=completion,
            cell_id=prior_id,
            run_dir=prior_root,
        )
        if adjudication.get("safe_to_continue") is not True:
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
) -> dict[str, Any]:
    observed = read_canonical_json(run_dir / "p0-cell-adjudication.json")
    expected = adjudicate_cell(
        completion=completion,
        cell_id=cell_id,
        run_dir=run_dir,
    )
    if observed != expected:
        raise ContractError(f"P0 cell adjudication drift: {cell_id}")
    return observed


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
    adjudication = adjudicate_cell(
        completion=completion,
        cell_id=cell_id,
        run_dir=run_dir,
    )
    atomic_install_json(
        run_dir,
        "p0-cell-adjudication.json",
        adjudication,
        quarantine_root=run_dir / "quarantine",
    )
    validate_cell_adjudication(
        completion=completion,
        cell_id=cell_id,
        run_dir=run_dir,
    )
    export_legacy_raw(run_dir, run_dir / "raw-results.json")
    return adjudication


def main() -> int:
    repository_root = Path(__file__).resolve().parents[2]
    ap = argparse.ArgumentParser(description="execute one integrated repaired-P0 cell")
    ap.add_argument("--preparation-root", required=True, type=Path)
    ap.add_argument("--cell", required=True, choices=CELL_ORDER)
    ap.add_argument("--acknowledge-complete-sha256", required=True)
    ap.add_argument("--poll-seconds", type=float, default=30.0)
    args = ap.parse_args()
    if len(args.acknowledge_complete_sha256) != 64:
        ap.error("--acknowledge-complete-sha256 must be a SHA-256")
    if not 1.0 <= args.poll_seconds <= 60.0:
        ap.error("--poll-seconds must be between 1 and 60")
    try:
        adjudication = execute_cell(
            repository_root=repository_root,
            preparation_root=args.preparation_root.resolve(strict=True),
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
