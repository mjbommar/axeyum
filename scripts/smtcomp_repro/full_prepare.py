"""Process-free preparation helpers for the credited full-population run.

The helpers in this module can materialize and revalidate the exact admitted
execution list and can construct registered host argv.  They have no solver,
SSH, systemd, or allocation-launch path.
"""

from __future__ import annotations

import copy
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from full_population import (
    FULL_LIST_SHA256,
    FULL_MANIFEST_SHA256,
    POPULATION_COUNT,
    SELECTED_FILES_SHA256,
    SHARD_COUNT,
    SOLVER_IDS,
    WALL_LIMIT_MS,
    build_schedule,
    validate_schedule,
)
from multi_host import (
    build_host_command,
    build_plan,
    install_host_command,
    prepare_run_directory,
    validate_host_command,
    validate_plan,
)
from resume_contract import ContractError, digest
from resume_fs import atomic_install_bytes, atomic_install_json, read_canonical_json
from resume_runner import (
    cgroup_run_manifest,
    official_selection_input_manifest,
    sha256_file,
    validate_source_identity,
)


SELECTION_SCHEMA = "axeyum.smtcomp-credited-full-selection-preparation.v1"
COMPOSITION_SCHEMA = "axeyum.smtcomp-credited-full-cell-composition.v1"
ACCEPTED_COMPLETION_SHA256 = (
    "322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698"
)
SELECTION_FIELDS = {
    "schema",
    "fixture_only",
    "launch_authorized",
    "accepted_selection_root",
    "accepted_completion_sha256",
    "selected_files_sha256",
    "population_count",
    "physical_bytes",
    "full_list_path",
    "full_list_sha256",
    "full_manifest_path",
    "full_manifest_sha256",
    "record_sha256",
}
COMPOSITION_FIELDS = {
    "schema",
    "fixture_only",
    "launch_authorized",
    "attempt_root",
    "selection_record_sha256",
    "source_identity_sha256",
    "cells",
    "record_sha256",
}
SOLVER_ENVIRONMENT = {
    "AYU_THREADS": "1",
    "OMP_NUM_THREADS": "1",
    "RAYON_NUM_THREADS": "1",
}


@dataclass(frozen=True)
class FullSolverCell:
    solver_id: str
    binary: Path
    version: str
    internal_timeout_ms: int | None = None


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _official_ids(accepted_root: Path) -> list[str]:
    try:
        rows = (accepted_root / "official-selected.txt").read_text(
            encoding="utf-8"
        ).splitlines()
    except (OSError, UnicodeDecodeError) as exc:
        raise ContractError("cannot read accepted full-population selection") from exc
    if not rows or rows != sorted(set(rows)):
        raise ContractError("accepted full-population selection is not strictly ordered")
    return rows


def materialize_full_selection(
    *,
    accepted_root: Path,
    corpus_root: Path,
    output_dir: Path,
    fixture_only: bool = False,
) -> dict[str, Any]:
    """Write and validate the full admitted list/manifest without launching work."""

    if type(fixture_only) is not bool:
        raise ContractError("fixture_only must be Boolean")
    accepted = accepted_root.resolve(strict=True)
    corpus = corpus_root.resolve(strict=True)
    output = output_dir.resolve(strict=True)
    benchmark_ids = _official_ids(accepted)
    paths = [corpus / benchmark_id for benchmark_id in benchmark_ids]
    list_path = output / "full-selected-absolute.txt"
    atomic_install_bytes(
        output,
        list_path.name,
        "".join(f"{path.resolve(strict=True)}\n" for path in paths).encode("utf-8"),
    )
    manifest_path = output / "full-selection-input-v2.json"
    manifest = official_selection_input_manifest(
        list_path, "non-incremental/", accepted
    )
    atomic_install_json(output, manifest_path.name, manifest)
    record = _sealed(
        {
            "schema": SELECTION_SCHEMA,
            "fixture_only": fixture_only,
            "launch_authorized": False,
            "accepted_selection_root": str(accepted),
            "accepted_completion_sha256": sha256_file(accepted / "complete.json"),
            "selected_files_sha256": sha256_file(accepted / "selected-files.jsonl"),
            "population_count": len(manifest["benchmarks"]),
            "physical_bytes": sum(row["input_bytes"] for row in manifest["benchmarks"]),
            "full_list_path": str(list_path.resolve(strict=True)),
            "full_list_sha256": sha256_file(list_path),
            "full_manifest_path": str(manifest_path.resolve(strict=True)),
            "full_manifest_sha256": sha256_file(manifest_path),
        }
    )
    return validate_full_selection(record)


def validate_full_selection(record: dict[str, Any]) -> dict[str, Any]:
    """Rehash the admitted source, selected payloads, list, and v2 manifest."""

    if set(record) != SELECTION_FIELDS or record.get("schema") != SELECTION_SCHEMA:
        raise ContractError("full selection preparation field/schema mismatch")
    if record.get("record_sha256") != _sealed(record)["record_sha256"]:
        raise ContractError("full selection preparation seal mismatch")
    if record.get("launch_authorized") is not False:
        raise ContractError("selection preparation cannot authorize launch")
    fixture_only = record.get("fixture_only")
    if type(fixture_only) is not bool:
        raise ContractError("selection preparation fixture flag mismatch")
    accepted = Path(record.get("accepted_selection_root", ""))
    list_path = Path(record.get("full_list_path", ""))
    manifest_path = Path(record.get("full_manifest_path", ""))
    for label, path in (
        ("accepted selection", accepted),
        ("full list", list_path),
        ("full manifest", manifest_path),
    ):
        if not path.is_absolute() or path.is_symlink() or not path.exists():
            raise ContractError(f"invalid {label} path")
    if not accepted.is_dir() or not list_path.is_file() or not manifest_path.is_file():
        raise ContractError("full selection preparation path type mismatch")
    expected_manifest = official_selection_input_manifest(
        list_path, "non-incremental/", accepted
    )
    if read_canonical_json(manifest_path) != expected_manifest:
        raise ContractError("full selection preparation manifest drift")
    observed = {
        "accepted_completion_sha256": sha256_file(accepted / "complete.json"),
        "selected_files_sha256": sha256_file(accepted / "selected-files.jsonl"),
        "population_count": len(expected_manifest["benchmarks"]),
        "physical_bytes": sum(
            row["input_bytes"] for row in expected_manifest["benchmarks"]
        ),
        "full_list_sha256": sha256_file(list_path),
        "full_manifest_sha256": sha256_file(manifest_path),
    }
    if any(record[field] != value for field, value in observed.items()):
        raise ContractError("full selection preparation artifact drift")
    if not fixture_only:
        frozen = {
            "accepted_completion_sha256": ACCEPTED_COMPLETION_SHA256,
            "selected_files_sha256": SELECTED_FILES_SHA256,
            "population_count": POPULATION_COUNT,
            "full_list_sha256": FULL_LIST_SHA256,
            "full_manifest_sha256": FULL_MANIFEST_SHA256,
        }
        if any(record[field] != value for field, value in frozen.items()):
            raise ContractError("live full selection differs from preregistration")
    return record


def full_host_argv(
    *,
    python_executable: Path,
    staged_source: Path,
    solver_id: str,
    solver_binary: Path,
    shard_ids: list[int],
    session_id: str,
    file_list: Path,
    run_manifest: Path,
    run_dir: Path,
    selection_manifest: Path,
    accepted_root: Path,
    corpus_manifest: Path,
    environment_manifest: Path,
    source_identity_manifest: Path,
    internal_timeout_ms: int | None = None,
    fixture_only: bool = False,
) -> list[str]:
    """Construct one exact, process-free host command for an allocation."""

    if solver_id not in SOLVER_IDS:
        raise ContractError("unknown full-population solver cell")
    if (
        not shard_ids
        or shard_ids != sorted(set(shard_ids))
        or any(type(shard) is not int or not 0 <= shard < SHARD_COUNT for shard in shard_ids)
    ):
        raise ContractError("invalid full-population host shard set")
    if not session_id or any(character.isspace() for character in session_id):
        raise ContractError("invalid full-population resource session")
    argv = [
        str(python_executable.resolve(strict=True)),
        "-B",
        str((staged_source / "compete.py").resolve(strict=True)),
        "--host-run",
        "--host-shards",
        ",".join(str(shard) for shard in shard_ids),
        "--host-session-id",
        session_id,
        "--file-list",
        str(file_list.resolve(strict=True)),
        "--solver",
        f"{solver_id}={solver_binary.resolve(strict=True)} {{bench}}",
        "--track",
        "single_query",
        "--wall-limit",
        str(WALL_LIMIT_MS // 1000),
        "--mem-gb",
        "8",
        "--cores",
        "1",
        "--run-manifest",
        str(run_manifest.resolve(strict=True)),
        "--run-dir",
        str(run_dir.resolve(strict=True)),
        "--selection-manifest",
        str(selection_manifest.resolve(strict=True)),
        "--official-selection-root",
        str(accepted_root.resolve(strict=True)),
        "--corpus-manifest",
        str(corpus_manifest.resolve(strict=True)),
        "--environment-manifest",
        str(environment_manifest.resolve(strict=True)),
        "--source-identity-manifest",
        str(source_identity_manifest.resolve(strict=True)),
    ]
    for key, value in SOLVER_ENVIRONMENT.items():
        argv.extend(["--solver-env", f"{key}={value}"])
    if internal_timeout_ms is not None:
        if solver_id != "axeyum" or internal_timeout_ms != 19_000:
            raise ContractError("invalid full-population internal timeout")
        argv.extend(["--internal-timeout-ms", str(internal_timeout_ms)])
    elif solver_id == "axeyum":
        raise ContractError("Axeyum full-population command requires its soft timeout")
    if fixture_only:
        argv.append("--allow-unadmitted-selection-fixture")
    argv.append("--quiet")
    return argv


def compose_full_cell_manifests(
    *,
    repository_root: Path,
    source_root: Path,
    shared_root: Path,
    attempt_root: Path,
    selection: dict[str, Any],
    corpus_manifest: Path,
    environment_manifest: Path,
    source_identity_manifest: Path,
    host_registrations: list[dict[str, Any]],
    solver_cells: list[FullSolverCell],
    fixture_only: bool = False,
) -> dict[str, Any]:
    """Publish run/plan/command manifests for all cells without starting them."""

    validate_full_selection(selection)
    if selection["fixture_only"] is not fixture_only:
        raise ContractError("selection/cell fixture scope mismatch")
    if [cell.solver_id for cell in solver_cells] != list(SOLVER_IDS):
        raise ContractError("full-population solver cells are missing or reordered")
    shared = shared_root.resolve(strict=True)
    attempt = attempt_root.resolve(strict=True)
    try:
        attempt.relative_to(shared)
    except ValueError as exc:
        raise ContractError("full-population attempt escapes shared root") from exc
    source = source_root.resolve(strict=True)
    source_identity_path = source_identity_manifest.resolve(strict=True)
    source_identity = read_canonical_json(source_identity_path)
    validate_source_identity(source_identity, source)
    corpus_path = corpus_manifest.resolve(strict=True)
    environment_path = environment_manifest.resolve(strict=True)
    environment_sha256 = sha256_file(environment_path)
    if (
        not isinstance(host_registrations, list)
        or len(host_registrations) != 3
        or any(
            row.get("environment_class_sha256") != environment_sha256
            for row in host_registrations
        )
    ):
        raise ContractError("full-population host environment registration mismatch")

    cells_root = attempt / "cells"
    inputs = attempt / "inputs"
    cells_root.mkdir(parents=True, exist_ok=True)
    inputs.mkdir(parents=True, exist_ok=True)
    results = []
    for cell in solver_cells:
        binary = cell.binary.resolve(strict=True)
        command_template = [str(binary), "{bench}"]
        if cell.internal_timeout_ms is not None:
            if cell.solver_id != "axeyum" or cell.internal_timeout_ms != 19_000:
                raise ContractError("invalid full-population cell timeout")
            command_template.extend(["--timeout-ms", str(cell.internal_timeout_ms)])
        elif cell.solver_id == "axeyum":
            raise ContractError("Axeyum full-population cell requires its soft timeout")
        run_path = inputs / f"{cell.solver_id}-run-manifest.json"
        run = cgroup_run_manifest(
            repository_root=repository_root,
            source_root=source,
            file_list=Path(selection["full_list_path"]),
            selection_manifest=Path(selection["full_manifest_path"]),
            corpus_manifest=corpus_path,
            environment_manifest=environment_path,
            solver_id=cell.solver_id,
            command_template=command_template,
            track="single_query",
            wall_limit_ms=WALL_LIMIT_MS,
            memory_limit_bytes=8 * 1024**3,
            cores=1,
            shard_count=SHARD_COUNT,
            worker_slots=2,
            aggregate_memory_bytes=16 * 1024**3,
            pids_max=64,
            multi_host=True,
            source_identity=source_identity,
            toolchain_identity=host_registrations[0]["toolchain_identity_sha256"],
            solver_environment=SOLVER_ENVIRONMENT,
        )
        atomic_install_json(inputs, run_path.name, run)
        schedule = validate_schedule(
            build_schedule(run["resource_enforcement"]["enforcement_id"])
        )
        run_dir = cells_root / cell.solver_id
        plan = build_plan(
            run=run,
            shared_root=shared,
            environment_class_sha256=environment_sha256,
            host_registrations=host_registrations,
            allocations=schedule["allocations"],
        )
        prepare_run_directory(plan=plan, run=run, run_dir=run_dir)
        plan_path = run_dir / "multi-host-plan.json"
        schedule_path = run_dir / "full-schedule.json"
        atomic_install_json(run_dir, plan_path.name, plan)
        atomic_install_json(run_dir, schedule_path.name, schedule)
        command_rows = []
        for allocation_row in schedule["allocations"]:
            allocation_id = allocation_row["allocation_id"]
            session_id = (
                f"full-{cell.solver_id}-{allocation_id}-{run['identity_sha256'][:12]}"
            )
            argv = full_host_argv(
                python_executable=Path(sys.executable),
                staged_source=source,
                solver_id=cell.solver_id,
                solver_binary=binary,
                shard_ids=allocation_row["shard_ids"],
                session_id=session_id,
                file_list=Path(selection["full_list_path"]),
                run_manifest=run_path,
                run_dir=run_dir,
                selection_manifest=Path(selection["full_manifest_path"]),
                accepted_root=Path(selection["accepted_selection_root"]),
                corpus_manifest=corpus_path,
                environment_manifest=environment_path,
                source_identity_manifest=source_identity_path,
                internal_timeout_ms=cell.internal_timeout_ms,
                fixture_only=fixture_only,
            )
            command = build_host_command(
                plan_path=plan_path,
                run_manifest_path=run_path,
                allocation_id=allocation_id,
                session_id=session_id,
                remote_helper_path=source / "multi_host.py",
                argv=argv,
                inspect_shared_root=not fixture_only,
            )
            validate_host_command(command, inspect_shared_root=not fixture_only)
            command_path = install_host_command(run_dir, command)
            command_rows.append(
                {
                    "allocation_id": allocation_id,
                    "generation": allocation_row["generation"],
                    "host_id": allocation_row["host_id"],
                    "shard_ids": allocation_row["shard_ids"],
                    "session_id": session_id,
                    "path": str(command_path.resolve(strict=True)),
                    "sha256": sha256_file(command_path),
                }
            )
        results.append(
            {
                "solver_id": cell.solver_id,
                "version": cell.version,
                "selection_record_sha256": selection["record_sha256"],
                "run_identity_sha256": run["identity_sha256"],
                "run_manifest_path": str(run_path.resolve(strict=True)),
                "run_manifest_sha256": sha256_file(run_path),
                "plan_sha256": plan["plan_sha256"],
                "plan_path": str(plan_path.resolve(strict=True)),
                "plan_file_sha256": sha256_file(plan_path),
                "schedule_record_sha256": schedule["record_sha256"],
                "schedule_path": str(schedule_path.resolve(strict=True)),
                "schedule_file_sha256": sha256_file(schedule_path),
                "commands": command_rows,
            }
        )
    composition = _sealed(
        {
            "schema": COMPOSITION_SCHEMA,
            "fixture_only": fixture_only,
            "launch_authorized": False,
            "attempt_root": str(attempt),
            "selection_record_sha256": selection["record_sha256"],
            "source_identity_sha256": source_identity["record_sha256"],
            "cells": results,
        }
    )
    return validate_full_cell_composition(
        composition,
        selection=selection,
        inspect_shared_root=not fixture_only,
    )


def validate_full_cell_composition(
    composition: dict[str, Any],
    *,
    selection: dict[str, Any],
    inspect_shared_root: bool = True,
) -> dict[str, Any]:
    """Revalidate every process-free run, plan, schedule, and host command."""

    validate_full_selection(selection)
    if (
        set(composition) != COMPOSITION_FIELDS
        or composition.get("schema") != COMPOSITION_SCHEMA
        or composition.get("record_sha256") != _sealed(composition)["record_sha256"]
    ):
        raise ContractError("full cell composition field/schema/seal mismatch")
    if (
        composition.get("launch_authorized") is not False
        or composition.get("fixture_only") is not selection["fixture_only"]
        or composition.get("selection_record_sha256") != selection["record_sha256"]
    ):
        raise ContractError("full cell composition scope mismatch")
    attempt = Path(composition.get("attempt_root", ""))
    if not attempt.is_absolute() or attempt.is_symlink() or not attempt.is_dir():
        raise ContractError("full cell composition attempt root mismatch")
    cells = composition.get("cells")
    if (
        not isinstance(cells, list)
        or [cell.get("solver_id") for cell in cells] != list(SOLVER_IDS)
    ):
        raise ContractError("full cell composition solver order mismatch")
    observed_schedules = set()
    for cell in cells:
        run_path = Path(cell.get("run_manifest_path", ""))
        plan_path = Path(cell.get("plan_path", ""))
        schedule_path = Path(cell.get("schedule_path", ""))
        for path in (run_path, plan_path, schedule_path):
            if not path.is_absolute() or path.is_symlink() or not path.is_file():
                raise ContractError("full cell composition artifact path mismatch")
            try:
                path.relative_to(attempt)
            except ValueError as exc:
                raise ContractError("full cell composition artifact escapes attempt") from exc
        run = read_canonical_json(run_path)
        plan = read_canonical_json(plan_path)
        schedule = validate_schedule(read_canonical_json(schedule_path))
        validate_plan(plan, run, inspect_shared_root=inspect_shared_root)
        if (
            cell.get("selection_record_sha256") != selection["record_sha256"]
            or cell.get("run_identity_sha256") != run.get("identity_sha256")
            or cell.get("run_manifest_sha256") != sha256_file(run_path)
            or cell.get("plan_sha256") != plan.get("plan_sha256")
            or cell.get("plan_file_sha256") != sha256_file(plan_path)
            or cell.get("schedule_record_sha256") != schedule["record_sha256"]
            or cell.get("schedule_file_sha256") != sha256_file(schedule_path)
            or plan.get("allocations") != schedule["allocations"]
        ):
            raise ContractError("full cell composition identity drift")
        resources = run.get("resource_enforcement", {})
        if (
            run.get("identity", {}).get("shard_count") != SHARD_COUNT
            or resources.get("worker_slots") != 2
            or resources.get("aggregate_memory_bytes") != 16 * 1024**3
            or resources.get("aggregate_cpu_quota_usec") != 200_000
            or resources.get("memory_swap_bytes") != 0
            or resources.get("pids_max") != 64
        ):
            raise ContractError("full cell composition resource drift")
        commands = cell.get("commands")
        expected_allocations = schedule["allocations"]
        if (
            not isinstance(commands, list)
            or len(commands) != len(expected_allocations)
            or [row.get("allocation_id") for row in commands]
            != [row["allocation_id"] for row in expected_allocations]
        ):
            raise ContractError("full cell composition command inventory mismatch")
        for command_row, allocation_row in zip(
            commands, expected_allocations, strict=True
        ):
            command_path = Path(command_row.get("path", ""))
            if (
                not command_path.is_absolute()
                or command_path.is_symlink()
                or not command_path.is_file()
                or command_row.get("sha256") != sha256_file(command_path)
                or command_row.get("generation") != allocation_row["generation"]
                or command_row.get("host_id") != allocation_row["host_id"]
                or command_row.get("shard_ids") != allocation_row["shard_ids"]
            ):
                raise ContractError("full cell composition command artifact drift")
            command = read_canonical_json(command_path)
            validate_host_command(
                command, inspect_shared_root=inspect_shared_root
            )
            if (
                command.get("allocation_id") != allocation_row["allocation_id"]
                or command.get("session_id") != command_row.get("session_id")
            ):
                raise ContractError("full cell composition command identity drift")
        run_root = attempt / "cells" / cell["solver_id"]
        if any((run_root / "multi-host-attempts").iterdir()) or any(
            (run_root / "multi-host-terminals").iterdir()
        ):
            raise ContractError("full cell composition unexpectedly contains attempts")
        observed_schedules.add(schedule["record_sha256"])
    if len(observed_schedules) != 1:
        raise ContractError("full cell composition schedules differ across solvers")
    return composition
