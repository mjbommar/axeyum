"""Preparation-only composer for the repaired full-library P0.

The module freezes every input needed by the preregistered three-cell run and
publishes completion last.  It deliberately has no allocation-launch import or
code path: execution remains a separate, post-review operator action.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from multi_host import (
    allocation,
    build_host_command,
    build_plan,
    environment_manifest,
    host_registration,
    install_host_command,
    prepare_run_directory,
    remote_probe,
    stage_execution_bundle,
    validate_execution_bundle,
    validate_host_command,
)
from resume_contract import ContractError, canonical_bytes, digest
from resume_fs import atomic_install_bytes, atomic_install_json, read_canonical_json
from resume_runner import (
    cgroup_run_manifest,
    official_selection_input_manifest,
    sha256_bytes,
    sha256_file,
)
from runner import run_solver


PREPARATION_SCHEMA = "axeyum.smtcomp-repaired-p0-preparation.v1"
CORPUS_SCHEMA = "axeyum.smtcomp-repaired-p0-corpus.v1"
SENTINEL_SCHEMA = "axeyum.smtcomp-incident-sentinel.v2"
SAFE_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}\Z")
P0_LOGICS = frozenset({"QF_FP", "QF_BVFP", "QF_ABVFP", "QF_AUFLIA"})
FP_LOGICS = frozenset({"QF_FP", "QF_BVFP", "QF_ABVFP"})
SOLVER_ENVIRONMENT = {
    "AYU_THREADS": "1",
    "OMP_NUM_THREADS": "1",
    "RAYON_NUM_THREADS": "1",
}
EXPECTED_SELECTION = {
    "all": {
        "count": 1810,
        "list_sha256": "e6da1f475ef2674a8461697babaa4e86bce9f3da9d3e7f9b03f0fbf146572e3d",
        "manifest_sha256": "a8cb9ba090b22e658e06dc53b4c97e1cdce595117acc1cbdc7f8476e9e85f4f4",
    },
    "fp": {
        "count": 1305,
        "list_sha256": "6025cf1dedfe7e425601f41f10e29ad594ddc083db3f997cb1303e93e70ca801",
        "manifest_sha256": "498184e470072824eaefe46092ff1b2c7228ee23c35b165800a9169a52026041",
    },
}
EXPECTED_ORACLES = {
    "cvc5": "7562a8b0b835e3eaad5f1a7b4616cd762350cf567b6be03d7e8ee24fa5ced5ee",
    "bitwuzla": "d98164badcd34c12ccbbd9e5aab9373854bb187e79f99ccda4ec2aa9951c0eab",
}
EXPECTED_SENTINELS = {
    "qf_abvfp": "6f0b87776052d1770e8503bcc593ad842cc649d533c41fa4a898808397524b8b",
    "qf_bvfp": "31ce580816bfb0647001f64ef480cdd779fe2f31da320354ea1ea63cd9da34ae",
    "qf_auflia": "dc7f8f51be688669321c8a9a15f2543fc070bc3a4c55b81c763604c34fa73bde",
}
HOSTS = (("s5", "s5"), ("s6", "s6"), ("s7", "s7"))
RETRY_HOSTS = {0: "s6", 1: "s7", 2: "s5"}


@dataclass(frozen=True)
class SolverCell:
    solver_id: str
    source_binary: Path
    version: str
    selection: str
    internal_timeout_ms: int | None = None


@dataclass(frozen=True)
class Sentinel:
    sentinel_id: str
    path: Path
    expected_sha256: str
    kind: str


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = dict(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _safe_attempt_id(value: str) -> str:
    if not SAFE_ID.fullmatch(value):
        raise ContractError("unsafe P0 preparation attempt ID")
    return value


def _require_clean_repository(root: Path) -> None:
    try:
        status = subprocess.check_output(
            ["git", "status", "--porcelain=v1", "--untracked-files=all"],
            cwd=root,
            stderr=subprocess.STDOUT,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ContractError("unable to inspect preparation repository") from exc
    if status:
        raise ContractError("P0 preparation requires a clean source worktree")


def _install_executable(source: Path, destination: Path) -> dict[str, Any]:
    resolved = source.resolve(strict=True)
    if not resolved.is_file() or not os.access(resolved, os.X_OK):
        raise ContractError(f"solver binary is missing or not executable: {source}")
    atomic_install_bytes(destination.parent, destination.name, resolved.read_bytes())
    destination.chmod(0o555)
    if sha256_file(destination) != sha256_file(resolved):
        raise ContractError("staged solver binary differs from its source")
    return {
        "source_path": str(resolved),
        "path": str(destination.resolve(strict=True)),
        "bytes": destination.stat().st_size,
        "sha256": sha256_file(destination),
    }


def _official_ids(accepted_root: Path) -> list[str]:
    try:
        rows = (accepted_root / "official-selected.txt").read_text(
            encoding="utf-8"
        ).splitlines()
    except (OSError, UnicodeDecodeError) as exc:
        raise ContractError("cannot read accepted official selection") from exc
    if not rows or rows != sorted(set(rows)):
        raise ContractError("accepted official selection is not strictly ordered")
    return rows


def build_selection_slice(
    *,
    accepted_root: Path,
    corpus_root: Path,
    output_dir: Path,
    name: str,
    logics: frozenset[str],
    expected: dict[str, Any] | None,
) -> dict[str, Any]:
    """Publish and revalidate one admitted, official-order execution slice."""

    paths = []
    for benchmark_id in _official_ids(accepted_root):
        parts = benchmark_id.split("/", 2)
        if len(parts) != 3:
            raise ContractError("malformed official benchmark identity")
        if parts[1] in logics:
            paths.append(corpus_root / benchmark_id)
    if not paths:
        raise ContractError("P0 selection slice is empty")
    list_path = output_dir / f"{name}-selected-absolute.txt"
    atomic_install_bytes(
        output_dir,
        list_path.name,
        "".join(f"{path.resolve(strict=True)}\n" for path in paths).encode("utf-8"),
    )
    manifest_path = output_dir / f"{name}-selection-input-v2.json"
    manifest = official_selection_input_manifest(
        list_path, "non-incremental/", accepted_root
    )
    atomic_install_json(output_dir, manifest_path.name, manifest)
    observed = {
        "name": name,
        "logics": sorted(logics),
        "count": len(paths),
        "list_path": str(list_path.resolve(strict=True)),
        "list_sha256": sha256_file(list_path),
        "manifest_path": str(manifest_path.resolve(strict=True)),
        "manifest_sha256": sha256_file(manifest_path),
    }
    if expected is not None and any(
        observed[field] != expected[field]
        for field in ("count", "list_sha256", "manifest_sha256")
    ):
        raise ContractError(f"{name} selection identity differs from preregistration")
    return observed


def _sentinel_outcome(
    *,
    solver: SolverCell,
    binary: Path,
    sentinel: Sentinel,
    output_dir: Path,
) -> dict[str, Any]:
    command = [str(binary), str(sentinel.path.resolve(strict=True))]
    if solver.internal_timeout_ms is not None:
        command.extend(["--timeout-ms", str(solver.internal_timeout_ms)])
    environment = os.environ.copy()
    environment.update(SOLVER_ENVIRONMENT)
    started_at_ns = time.time_ns()
    result = run_solver(
        command,
        wall_limit_s=20.0,
        mem_limit_bytes=8 * 1024**3,
        env=environment,
    )
    ended_at_ns = time.time_ns()
    stem = f"{sentinel.sentinel_id}-{solver.solver_id}"
    stdout_path = output_dir / f"{stem}.stdout"
    stderr_path = output_dir / f"{stem}.stderr"
    atomic_install_bytes(output_dir, stdout_path.name, result.stdout_bytes)
    atomic_install_bytes(output_dir, stderr_path.name, result.stderr_bytes)
    return _sealed(
        {
            "schema": SENTINEL_SCHEMA,
            "sentinel_id": sentinel.sentinel_id,
            "sentinel_kind": sentinel.kind,
            "sentinel_path": str(sentinel.path.resolve(strict=True)),
            "sentinel_sha256": sha256_file(sentinel.path),
            "solver_id": solver.solver_id,
            "solver_binary_sha256": sha256_file(binary),
            "command_sha256": digest(command),
            "environment_sha256": digest(SOLVER_ENVIRONMENT),
            "observed_status": result.observed.value if result.observed else None,
            "termination_class": result.termination_class,
            "exit_code": result.exit_code,
            "signal": result.signal,
            "resource_limit_kind": result.resource_limit_kind,
            "started_at_ns": started_at_ns,
            "ended_at_ns": ended_at_ns,
            "wall_time_ns": round(result.scoring_wall_time * 1_000_000_000),
            "runner_elapsed_ns": round(result.runner_elapsed * 1_000_000_000),
            "stdout_path": str(stdout_path.resolve(strict=True)),
            "stdout_sha256": sha256_file(stdout_path),
            "stdout_bytes": stdout_path.stat().st_size,
            "stderr_path": str(stderr_path.resolve(strict=True)),
            "stderr_sha256": sha256_file(stderr_path),
            "stderr_bytes": stderr_path.stat().st_size,
        }
    )


def run_sentinels(
    *,
    solvers: list[SolverCell],
    copied_binaries: dict[str, Path],
    sentinels: list[Sentinel],
    output_dir: Path,
) -> list[dict[str, Any]]:
    """Run the preregistered incident matrix and reject unsafe outcomes."""

    by_id = {solver.solver_id: solver for solver in solvers}
    matrix = {
        "qf_abvfp": ("axeyum", "cvc5", "bitwuzla"),
        "qf_bvfp": ("axeyum", "cvc5", "bitwuzla"),
        "qf_auflia": ("axeyum", "cvc5"),
    }
    records = []
    for sentinel in sentinels:
        if sha256_file(sentinel.path) != sentinel.expected_sha256:
            raise ContractError(f"sentinel bytes differ: {sentinel.sentinel_id}")
        try:
            solver_ids = matrix[sentinel.kind]
        except KeyError as exc:
            raise ContractError("unsupported sentinel kind") from exc
        for solver_id in solver_ids:
            record = _sentinel_outcome(
                solver=by_id[solver_id],
                binary=copied_binaries[solver_id],
                sentinel=sentinel,
                output_dir=output_dir,
            )
            status = record["observed_status"]
            completed = (
                record["termination_class"] == "completed"
                and record["exit_code"] == 0
            )
            if sentinel.kind in {"qf_abvfp", "qf_bvfp"} and (
                status != "unsat" or not completed
            ):
                raise ContractError(f"FP incident sentinel failed: {solver_id}")
            if sentinel.kind == "qf_auflia":
                if solver_id == "cvc5" and (status != "sat" or not completed):
                    raise ContractError("cvc5 AUFLIA sentinel failed")
                if solver_id == "axeyum" and not (
                    completed and status in {"sat", "unknown"}
                    or record["termination_class"] == "wall-timeout"
                    and status is None
                ):
                    raise ContractError("Axeyum AUFLIA sentinel was not safe")
            records.append(record)
    return records


def _allocations(enforcement_id: str) -> list[dict[str, Any]]:
    rows = [
        allocation(
            allocation_id=f"initial-{shard}",
            generation=0,
            host_id=HOSTS[shard][0],
            shard_ids=[shard],
            enforcement_id=enforcement_id,
        )
        for shard in range(3)
    ]
    rows.extend(
        allocation(
            allocation_id=f"retry-{shard}",
            generation=1,
            host_id=RETRY_HOSTS[shard],
            shard_ids=[shard],
            enforcement_id=enforcement_id,
            recovers_allocation_id=f"initial-{shard}",
        )
        for shard in range(3)
    )
    return rows


def _command_argv(
    *,
    staged: Path,
    cell: SolverCell,
    binary: Path,
    selection: dict[str, Any],
    accepted_root: Path,
    corpus_manifest: Path,
    environment_path: Path,
    run_path: Path,
    run_dir: Path,
    shard: int,
    session_id: str,
) -> list[str]:
    argv = [
        sys.executable,
        "-B",
        str(staged / "scripts" / "smtcomp_repro" / "compete.py"),
        "--host-run",
        "--host-shards",
        str(shard),
        "--host-session-id",
        session_id,
        "--file-list",
        selection["list_path"],
        "--solver",
        f"{cell.solver_id}={binary} {{bench}}",
        "--track",
        "single_query",
        "--wall-limit",
        "20",
        "--mem-gb",
        "8",
        "--cores",
        "1",
        "--run-manifest",
        str(run_path),
        "--run-dir",
        str(run_dir),
        "--selection-manifest",
        selection["manifest_path"],
        "--official-selection-root",
        str(accepted_root),
        "--corpus-manifest",
        str(corpus_manifest),
        "--environment-manifest",
        str(environment_path),
        "--source-identity-manifest",
        str(staged / "source-identity.json"),
        "--solver-env",
        "AYU_THREADS=1",
        "--solver-env",
        "OMP_NUM_THREADS=1",
        "--solver-env",
        "RAYON_NUM_THREADS=1",
        "--quiet",
    ]
    if cell.internal_timeout_ms is not None:
        argv.extend(["--internal-timeout-ms", str(cell.internal_timeout_ms)])
    return argv


def _artifact(path: Path, root: Path) -> dict[str, Any]:
    resolved = path.resolve(strict=True)
    return {
        "path": str(resolved.relative_to(root)),
        "bytes": resolved.stat().st_size,
        "sha256": sha256_file(resolved),
    }


def prepare_p0(
    *,
    repository_root: Path,
    source_root: Path,
    shared_root: Path,
    accepted_root: Path,
    corpus_root: Path,
    source_corpus_manifest: Path,
    attempt_id: str,
    solvers: list[SolverCell],
    sentinels: list[Sentinel],
    observations: list[dict[str, Any]],
    expected_selection: dict[str, dict[str, Any]] | None = EXPECTED_SELECTION,
    expected_oracles: dict[str, str] | None = EXPECTED_ORACLES,
    require_clean: bool = True,
) -> Path:
    """Publish one immutable, non-launching P0 preparation attempt."""

    if require_clean:
        _require_clean_repository(repository_root)
    shared = shared_root.resolve(strict=True)
    accepted = accepted_root.resolve(strict=True)
    corpus = corpus_root.resolve(strict=True)
    for path in (accepted, corpus, source_corpus_manifest.resolve(strict=True)):
        try:
            path.relative_to(shared)
        except ValueError as exc:
            raise ContractError("P0 input escapes the registered shared root") from exc
    attempt = shared / _safe_attempt_id(attempt_id)
    attempt.mkdir(mode=0o755)
    inputs = attempt / "inputs"
    binaries = attempt / "binaries"
    sentinel_outputs = attempt / "sentinels" / "outputs"
    for directory in (inputs, binaries, sentinel_outputs):
        directory.mkdir(parents=True, mode=0o755)

    source_parent = shared / "source-bundles"
    source_parent.mkdir(mode=0o755, exist_ok=True)
    staged, source_identity = stage_execution_bundle(
        repository_root=repository_root,
        source_root=source_root,
        fixture_root=source_root / "fixtures" / "e3",
        staging_parent=source_parent,
    )
    environment = environment_manifest(observations)
    environment_path = inputs / "environment.json"
    atomic_install_json(inputs, environment_path.name, environment)
    environment_sha = sha256_file(environment_path)
    registrations = [
        host_registration(
            host_id=host_id,
            ssh_target=target,
            observation=observation,
            environment_sha256=environment_sha,
        )
        for (host_id, target), observation in zip(HOSTS, observations, strict=True)
    ]
    if sha256_file(Path(sys.executable)) != observations[0]["python_executable_sha256"]:
        raise ContractError("coordinator and P0 hosts have different Python bytes")

    selections = {
        "all": build_selection_slice(
            accepted_root=accepted,
            corpus_root=corpus,
            output_dir=inputs,
            name="all",
            logics=P0_LOGICS,
            expected=None if expected_selection is None else expected_selection["all"],
        ),
        "fp": build_selection_slice(
            accepted_root=accepted,
            corpus_root=corpus,
            output_dir=inputs,
            name="fp",
            logics=FP_LOGICS,
            expected=None if expected_selection is None else expected_selection["fp"],
        ),
    }
    corpus_manifest = inputs / "corpus.json"
    atomic_install_json(
        inputs,
        corpus_manifest.name,
        _sealed(
            {
                "schema": CORPUS_SCHEMA,
                "corpus_root": str(corpus),
                "source_manifest_path": str(source_corpus_manifest.resolve(strict=True)),
                "source_manifest_sha256": sha256_file(source_corpus_manifest),
                "accepted_selection_root": str(accepted),
                "accepted_completion_sha256": sha256_file(accepted / "complete.json"),
            }
        ),
    )

    binary_rows = []
    copied = {}
    for cell in solvers:
        destination = binaries / cell.solver_id
        row = _install_executable(cell.source_binary, destination)
        row.update({"solver_id": cell.solver_id, "version": cell.version})
        if (
            expected_oracles is not None
            and cell.solver_id in expected_oracles
            and row["sha256"] != expected_oracles[cell.solver_id]
        ):
            raise ContractError(f"{cell.solver_id} binary differs from preregistration")
        copied[cell.solver_id] = destination
        binary_rows.append(row)

    sentinel_records = run_sentinels(
        solvers=solvers,
        copied_binaries=copied,
        sentinels=sentinels,
        output_dir=sentinel_outputs,
    )
    atomic_install_json(attempt / "sentinels", "sentinel-records.json", sentinel_records)

    cells = []
    for cell in solvers:
        run_dir = attempt / "cells" / cell.solver_id
        run_path = inputs / f"{cell.solver_id}-run-manifest.json"
        command_template = [str(copied[cell.solver_id]), "{bench}"]
        if cell.internal_timeout_ms is not None:
            command_template.extend(["--timeout-ms", str(cell.internal_timeout_ms)])
        selection = selections[cell.selection]
        run = cgroup_run_manifest(
            repository_root=repository_root,
            source_root=staged / "scripts" / "smtcomp_repro",
            file_list=Path(selection["list_path"]),
            selection_manifest=Path(selection["manifest_path"]),
            corpus_manifest=corpus_manifest,
            environment_manifest=environment_path,
            solver_id=cell.solver_id,
            command_template=command_template,
            track="single_query",
            wall_limit_ms=20_000,
            memory_limit_bytes=8 * 1024**3,
            cores=1,
            shard_count=3,
            worker_slots=1,
            aggregate_memory_bytes=8 * 1024**3,
            pids_max=32,
            multi_host=True,
            source_identity=source_identity,
            toolchain_identity=observations[0]["toolchain_identity_sha256"],
            solver_environment=SOLVER_ENVIRONMENT,
        )
        atomic_install_json(inputs, run_path.name, run)
        plan = build_plan(
            run=run,
            shared_root=shared,
            environment_class_sha256=environment_sha,
            host_registrations=registrations,
            allocations=_allocations(run["resource_enforcement"]["enforcement_id"]),
        )
        prepare_run_directory(plan=plan, run=run, run_dir=run_dir)
        plan_path = run_dir / "multi-host-plan.json"
        atomic_install_json(run_dir, plan_path.name, plan)
        command_rows = []
        allocations = {row["allocation_id"]: row for row in plan["allocations"]}
        for allocation_id in sorted(allocations):
            row = allocations[allocation_id]
            shard = row["shard_ids"][0]
            session_id = (
                f"p0-{cell.solver_id}-{allocation_id}-{run['identity_sha256'][:12]}"
            )
            command = build_host_command(
                plan_path=plan_path,
                run_manifest_path=run_path,
                allocation_id=allocation_id,
                session_id=session_id,
                remote_helper_path=staged
                / "scripts"
                / "smtcomp_repro"
                / "multi_host.py",
                argv=_command_argv(
                    staged=staged,
                    cell=cell,
                    binary=copied[cell.solver_id],
                    selection=selection,
                    accepted_root=accepted,
                    corpus_manifest=corpus_manifest,
                    environment_path=environment_path,
                    run_path=run_path,
                    run_dir=run_dir,
                    shard=shard,
                    session_id=session_id,
                ),
            )
            validate_host_command(command)
            command_path = install_host_command(run_dir, command)
            command_rows.append(
                {
                    "allocation_id": allocation_id,
                    "host_id": row["host_id"],
                    "generation": row["generation"],
                    "shard_ids": row["shard_ids"],
                    "path": str(command_path.resolve(strict=True)),
                    "sha256": sha256_file(command_path),
                }
            )
        cells.append(
            {
                "solver_id": cell.solver_id,
                "attempt_root": str(run_dir.resolve(strict=True)),
                "selection": cell.selection,
                "run_identity_sha256": run["identity_sha256"],
                "run_manifest_path": str(run_path.resolve(strict=True)),
                "run_manifest_sha256": sha256_file(run_path),
                "plan_sha256": plan["plan_sha256"],
                "plan_file_sha256": sha256_file(plan_path),
                "commands": command_rows,
            }
        )

    artifacts = [
        _artifact(path, attempt)
        for path in sorted(attempt.rglob("*"))
        if path.is_file() and path.name != "complete.json"
    ]
    completion = _sealed(
        {
            "schema": PREPARATION_SCHEMA,
            "status": "prepared-no-launch",
            "launch_authorized": False,
            "attempt_root": str(attempt.resolve(strict=True)),
            "prepared_at_ns": time.time_ns(),
            "accepted_selection_root": str(accepted),
            "accepted_completion_sha256": sha256_file(accepted / "complete.json"),
            "source_bundle_root": str(staged),
            "source_identity_sha256": source_identity["record_sha256"],
            "repository_commit": source_identity["repository_commit"],
            "environment_sha256": environment_sha,
            "solver_environment": SOLVER_ENVIRONMENT,
            "selections": selections,
            "binaries": binary_rows,
            "sentinels": sentinel_records,
            "cells": cells,
            "artifacts": artifacts,
        }
    )
    atomic_install_json(attempt, "complete.json", completion)
    validate_preparation(attempt)
    return attempt


def validate_preparation(
    attempt: Path, *, require_empty: bool = True
) -> dict[str, Any]:
    completion = read_canonical_json(attempt / "complete.json")
    if completion.get("schema") != PREPARATION_SCHEMA:
        raise ContractError("P0 preparation schema mismatch")
    unsealed = dict(completion)
    claimed = unsealed.pop("record_sha256", None)
    if claimed != digest(unsealed):
        raise ContractError("P0 preparation record hash mismatch")
    if (
        completion.get("status") != "prepared-no-launch"
        or completion.get("launch_authorized") is not False
        or completion.get("attempt_root") != str(attempt.resolve(strict=True))
    ):
        raise ContractError("P0 preparation state mismatch")
    validate_execution_bundle(Path(completion["source_bundle_root"]))
    for row in completion.get("artifacts", []):
        path = attempt / row["path"]
        if (
            not path.is_file()
            or path.stat().st_size != row["bytes"]
            or sha256_file(path) != row["sha256"]
        ):
            raise ContractError(f"P0 preparation artifact drift: {row['path']}")
    if require_empty:
        for cell in completion.get("cells", []):
            run_root = Path(cell["attempt_root"])
            if any((run_root / "records").iterdir()):
                raise ContractError("P0 preparation unexpectedly contains solver records")
    return completion


def _default_attempt_id(repository_root: Path) -> str:
    commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repository_root, text=True
    ).strip()
    return f"repaired-p0-prep-{time.time_ns()}-{commit[:12]}"


def main() -> int:
    root = Path(__file__).resolve().parents[2]
    source = root / "scripts" / "smtcomp_repro"
    ap = argparse.ArgumentParser(description="prepare repaired SMT-COMP P0 without launch")
    ap.add_argument("--shared-root", required=True, type=Path)
    ap.add_argument("--accepted-selection", required=True, type=Path)
    ap.add_argument("--corpus-root", required=True, type=Path)
    ap.add_argument("--corpus-manifest", required=True, type=Path)
    ap.add_argument("--axeyum-binary", required=True, type=Path)
    ap.add_argument("--cvc5-binary", required=True, type=Path)
    ap.add_argument("--bitwuzla-binary", required=True, type=Path)
    ap.add_argument("--qf-abvfp-sentinel", required=True, type=Path)
    ap.add_argument("--qf-bvfp-sentinel", required=True, type=Path)
    ap.add_argument("--qf-auflia-sentinel", required=True, type=Path)
    ap.add_argument("--attempt-id", default=None)
    args = ap.parse_args()
    attempt_id = args.attempt_id or _default_attempt_id(root)
    try:
        shared = args.shared_root.resolve(strict=True)
        _require_clean_repository(root)
        source_parent = shared / "source-bundles"
        source_parent.mkdir(mode=0o755, exist_ok=True)
        staged, _identity = stage_execution_bundle(
            repository_root=root,
            source_root=source,
            fixture_root=source / "fixtures" / "e3",
            staging_parent=source_parent,
        )
        helper = staged / "scripts" / "smtcomp_repro" / "multi_host.py"
        observations = [
            remote_probe(
                ssh_target=target,
                remote_helper_path=helper,
                shared_root=shared,
            )
            for _host_id, target in HOSTS
        ]
        attempt = prepare_p0(
            repository_root=root,
            source_root=source,
            shared_root=shared,
            accepted_root=args.accepted_selection,
            corpus_root=args.corpus_root,
            source_corpus_manifest=args.corpus_manifest,
            attempt_id=attempt_id,
            solvers=[
                SolverCell("axeyum", args.axeyum_binary, "integrated-release", "all", 19_000),
                SolverCell("cvc5", args.cvc5_binary, "1.3.4", "all"),
                SolverCell("bitwuzla", args.bitwuzla_binary, "0.9.1", "fp"),
            ],
            sentinels=[
                Sentinel(
                    "qf-abvfp-query-26",
                    args.qf_abvfp_sentinel,
                    EXPECTED_SENTINELS["qf_abvfp"],
                    "qf_abvfp",
                ),
                Sentinel(
                    "qf-bvfp-query-26",
                    args.qf_bvfp_sentinel,
                    EXPECTED_SENTINELS["qf_bvfp"],
                    "qf_bvfp",
                ),
                Sentinel(
                    "qf-auflia-pipeline-invalid",
                    args.qf_auflia_sentinel,
                    EXPECTED_SENTINELS["qf_auflia"],
                    "qf_auflia",
                ),
            ],
            observations=observations,
        )
    except (ContractError, OSError, subprocess.CalledProcessError) as exc:
        print(f"P0 preparation rejected: {exc}", file=sys.stderr)
        return 2
    completion = read_canonical_json(attempt / "complete.json")
    print(canonical_bytes(completion).decode("utf-8"), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
