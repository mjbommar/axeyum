"""Opt-in E1b/E2 adapter from ``compete.py`` to resumable v2 evidence.

E1b proves the active runner, immutable checkpoints, attempt lifecycle, output
sidecars, and compatibility export on fixtures. E2 binds and validates the
real one-host aggregate enforcement descriptor and active cgroup session before
measurement shard execution.
"""

from __future__ import annotations

import hashlib
import json
import os
import platform
import re
import socket
import subprocess
import sys
import time
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable

from resume_contract import (
    RESULT_SCHEMA,
    VERDICT_POLICY,
    ContractError,
    canonical_bytes,
    digest,
    record_set_sha256,
    result_key,
    seal_record,
    validate_record,
    validate_run,
)
from resume_fs import (
    LeaseConflict,
    acquire_shard_lease,
    atomic_install_bytes,
    atomic_install_json,
    load_bundle,
    read_canonical_json,
    recover_orphan_temporaries,
    release_shard_lease,
    validate_bundle_directory,
    verify_output_sidecars,
)
from resource_enforcement import (
    CGROUP_KIND,
    FIXTURE_KIND,
    MULTI_HOST_KIND,
    cgroup_enforcement,
    cgroup_snapshot,
    fixture_enforcement,
    resource_policy_for,
    validate_enforcement,
    validate_snapshot,
)
from runner import RunResult, run_solver_metered
from smtlib_meta import read_meta


SELECTION_INPUT_SCHEMA = "axeyum.smtcomp-selection-input.v1"
OFFICIAL_SELECTION_INPUT_SCHEMA = "axeyum.smtcomp-selection-input.v2"
OFFICIAL_SELECTION_SCHEMA = "axeyum-smtcomp-official-selection-v1"
SELECTION_SCHEMA = "axeyum.smtcomp-run-selection.v1"
SOURCE_IDENTITY_SCHEMA = "axeyum.smtcomp-source-identity.v1"
SOURCE_IDENTITY_FIELDS = {
    "schema",
    "repository_commit",
    "source_tree_state_sha256",
    "runner_source_sha256",
    "record_sha256",
}
OUTPUT_CAPTURE_POLICY = {
    "capture": "exact-stdout-stderr-bytes",
    "parser": "last-sat-unsat-unknown-token-v1",
    "sidecars": "sha256-content-addressed",
}
SOLVER_ENVIRONMENT_KEY = re.compile(r"[A-Z][A-Z0-9_]{0,63}\Z")
RUNNER_SOURCE_NAMES = (
    "compete.py",
    "multi_host.py",
    "p0_prepare.py",
    "resume_contract.py",
    "resume_fs.py",
    "resume_runner.py",
    "resource_enforcement.py",
    "runner.py",
    "scoring.py",
    "smtlib_meta.py",
)


@dataclass(frozen=True)
class BenchmarkInput:
    sequence: int
    path: str
    benchmark_id: str
    benchmark_sha256: str
    input_bytes: int
    result_key: str
    logic: str
    expected_status: str | None
    num_named_assertions: int | None

    def artifact(self) -> dict[str, Any]:
        return {
            "sequence": self.sequence,
            "path": self.path,
            "benchmark_id": self.benchmark_id,
            "benchmark_sha256": self.benchmark_sha256,
            "input_bytes": self.input_bytes,
            "result_key": self.result_key,
            "logic": self.logic,
            "expected_status": self.expected_status,
            "num_named_assertions": self.num_named_assertions,
        }


Runner = Callable[..., RunResult]
PhaseHook = Callable[[str], None]


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def _is_sha256(value: object) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def _run_git(root: Path, *args: str) -> bytes:
    try:
        return subprocess.check_output(
            ["git", *args], cwd=root, stderr=subprocess.STDOUT
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ContractError(f"unable to inspect repository state: git {' '.join(args)}") from exc


def repository_commit(root: Path) -> str:
    return _run_git(root, "rev-parse", "HEAD").decode("ascii").strip()


def source_tree_state_sha256(root: Path) -> str:
    status = _run_git(root, "status", "--porcelain=v1", "-z", "--untracked-files=all")
    changed = _run_git(
        root, "ls-files", "-m", "-o", "--exclude-standard", "-z"
    ).split(b"\0")
    files = []
    for encoded in sorted(path for path in changed if path):
        relative = encoded.decode("utf-8", errors="surrogateescape")
        path = root / relative
        if path.is_symlink():
            content_sha256 = sha256_bytes(os.readlink(path).encode("utf-8"))
        elif path.is_file():
            content_sha256 = sha256_file(path)
        else:
            content_sha256 = None
        files.append({"path": relative, "sha256": content_sha256})
    return digest(
        {
            "repository_commit": repository_commit(root),
            "status_sha256": sha256_bytes(status),
            "changed_files": files,
        }
    )


def toolchain_identity_sha256() -> str:
    return digest(
        {
            "implementation": platform.python_implementation(),
            "python": platform.python_version(),
            "executable_sha256": sha256_file(Path(sys.executable).resolve()),
            "platform": platform.platform(),
        }
    )


def runner_source_sha256(source_root: Path) -> str:
    entries = []
    for name in RUNNER_SOURCE_NAMES:
        path = source_root / name
        entries.append({"path": name, "sha256": sha256_file(path)})
    return digest(entries)


def source_identity_artifact(
    repository_root: Path, source_root: Path
) -> dict[str, Any]:
    artifact = {
        "schema": SOURCE_IDENTITY_SCHEMA,
        "repository_commit": repository_commit(repository_root),
        "source_tree_state_sha256": source_tree_state_sha256(repository_root),
        "runner_source_sha256": runner_source_sha256(source_root),
    }
    artifact["record_sha256"] = digest(artifact)
    return artifact


def validate_source_identity(
    artifact: dict[str, Any], source_root: Path
) -> dict[str, Any]:
    if set(artifact) != SOURCE_IDENTITY_FIELDS:
        raise ContractError("source identity field set mismatch")
    if artifact.get("schema") != SOURCE_IDENTITY_SCHEMA:
        raise ContractError("source identity schema mismatch")
    unsealed = dict(artifact)
    claimed = unsealed.pop("record_sha256")
    if claimed != digest(unsealed):
        raise ContractError("source identity hash mismatch")
    if artifact["runner_source_sha256"] != runner_source_sha256(source_root):
        raise ContractError("source identity runner digest mismatch")
    for field in ("repository_commit", "source_tree_state_sha256"):
        value = artifact.get(field)
        if not isinstance(value, str) or not value:
            raise ContractError(f"invalid source identity field: {field}")
    return artifact


def solver_command_sha256(command_template: list[str]) -> str:
    return digest(command_template)


def normalize_solver_environment(
    environment: dict[str, str] | None,
) -> dict[str, str]:
    """Validate and canonicalize the explicit solver-process environment overlay."""

    normalized = {} if environment is None else dict(environment)
    if any(
        not isinstance(key, str)
        or not SOLVER_ENVIRONMENT_KEY.fullmatch(key)
        or not isinstance(value, str)
        or "\0" in value
        or "\n" in value
        for key, value in normalized.items()
    ):
        raise ContractError("invalid solver environment overlay")
    return {key: normalized[key] for key in sorted(normalized)}


def _solver_binary(command_template: list[str]) -> Path:
    if not command_template or "{bench}" in command_template[0]:
        raise ContractError("solver command has no fixed executable")
    binary = Path(command_template[0]).resolve()
    if not binary.is_file() or not os.access(binary, os.X_OK):
        raise ContractError(f"solver executable is missing or not executable: {binary}")
    return binary


def _run_manifest(
    *,
    repository_root: Path,
    source_root: Path,
    file_list: Path,
    selection_manifest: Path,
    corpus_manifest: Path,
    environment_manifest: Path,
    solver_id: str,
    command_template: list[str],
    track: str,
    wall_limit_ms: int,
    memory_limit_bytes: int,
    cores: int,
    shard_count: int,
    enforcement: dict[str, Any],
    solver_environment: dict[str, str] | None = None,
    source_identity: dict[str, Any] | None = None,
    toolchain_identity: str | None = None,
) -> dict[str, Any]:
    source = (
        source_identity_artifact(repository_root, source_root)
        if source_identity is None
        else validate_source_identity(source_identity, source_root)
    )
    binary_sha256 = sha256_file(_solver_binary(command_template))
    command_sha256 = solver_command_sha256(command_template)
    environment = normalize_solver_environment(solver_environment)
    environment_sha256 = digest(environment)
    solver_config_sha256 = digest(
        {
            "solver_id": solver_id,
            "solver_binary_sha256": binary_sha256,
            "solver_command_sha256": command_sha256,
            "solver_environment_sha256": environment_sha256,
        }
    )
    identity = {
        "contract_schema": "axeyum.smtcomp-resumable-run-contract.v2",
        "run_schema": "axeyum.smtcomp-run.v2",
        "result_schema": RESULT_SCHEMA,
        "selection_manifest_sha256": sha256_file(selection_manifest),
        "selected_list_sha256": sha256_file(file_list),
        "corpus_identity_sha256": sha256_file(corpus_manifest),
        "solver_id": solver_id,
        "solver_binary_sha256": binary_sha256,
        "solver_command_sha256": command_sha256,
        "solver_environment_sha256": environment_sha256,
        "solver_config_sha256": solver_config_sha256,
        "runner_source_sha256": source["runner_source_sha256"],
        "repository_commit": source["repository_commit"],
        "source_tree_state_sha256": source["source_tree_state_sha256"],
        "toolchain_identity_sha256": (
            toolchain_identity_sha256()
            if toolchain_identity is None
            else toolchain_identity
        ),
        "track": track,
        "wall_limit_ms": wall_limit_ms,
        "cpu_limit_ms": wall_limit_ms * cores,
        "memory_limit_bytes": memory_limit_bytes,
        "cores": cores,
        "shard_count": shard_count,
        "shard_mapping": "striped-index-v1",
        "environment_class_sha256": sha256_file(environment_manifest),
        "resource_enforcement_sha256": digest(enforcement),
        "resource_policy_sha256": digest(resource_policy_for(enforcement)),
        "output_capture_policy_sha256": digest(OUTPUT_CAPTURE_POLICY),
        "verdict_policy": VERDICT_POLICY,
    }
    run = {
        "schema": "axeyum.smtcomp-run.v2",
        "identity": identity,
        "identity_sha256": digest(identity),
        "resource_enforcement": enforcement,
    }
    validate_run(run)
    return run


def fixture_run_manifest(
    *,
    repository_root: Path,
    source_root: Path,
    file_list: Path,
    selection_manifest: Path,
    corpus_manifest: Path,
    environment_manifest: Path,
    solver_id: str,
    command_template: list[str],
    track: str,
    wall_limit_ms: int,
    memory_limit_bytes: int,
    cores: int,
    shard_count: int,
    solver_environment: dict[str, str] | None = None,
) -> dict[str, Any]:
    """Build a canonical E1b fake-run manifest for executable gate fixtures."""

    return _run_manifest(
        repository_root=repository_root,
        source_root=source_root,
        file_list=file_list,
        selection_manifest=selection_manifest,
        corpus_manifest=corpus_manifest,
        environment_manifest=environment_manifest,
        solver_id=solver_id,
        command_template=command_template,
        track=track,
        wall_limit_ms=wall_limit_ms,
        memory_limit_bytes=memory_limit_bytes,
        cores=cores,
        shard_count=shard_count,
        solver_environment=solver_environment,
        enforcement=fixture_enforcement(memory_limit_bytes),
    )


def cgroup_run_manifest(
    *,
    repository_root: Path,
    source_root: Path,
    file_list: Path,
    selection_manifest: Path,
    corpus_manifest: Path,
    environment_manifest: Path,
    solver_id: str,
    command_template: list[str],
    track: str,
    wall_limit_ms: int,
    memory_limit_bytes: int,
    cores: int,
    shard_count: int,
    worker_slots: int,
    aggregate_memory_bytes: int,
    pids_max: int,
    multi_host: bool = False,
    source_identity: dict[str, Any] | None = None,
    toolchain_identity: str | None = None,
    solver_environment: dict[str, str] | None = None,
) -> dict[str, Any]:
    """Build a canonical E2/E3 cgroup-backed measurement manifest."""

    enforcement = cgroup_enforcement(
        worker_slots=worker_slots,
        aggregate_memory_bytes=aggregate_memory_bytes,
        aggregate_cpu_cores=worker_slots * cores,
        pids_max=pids_max,
        unit_prefix="axeyum-smtcomp-e3" if multi_host else "axeyum-smtcomp-e2",
        multi_host=multi_host,
    )
    return _run_manifest(
        repository_root=repository_root,
        source_root=source_root,
        file_list=file_list,
        selection_manifest=selection_manifest,
        corpus_manifest=corpus_manifest,
        environment_manifest=environment_manifest,
        solver_id=solver_id,
        command_template=command_template,
        track=track,
        wall_limit_ms=wall_limit_ms,
        memory_limit_bytes=memory_limit_bytes,
        cores=cores,
        shard_count=shard_count,
        solver_environment=solver_environment,
        enforcement=enforcement,
        source_identity=source_identity,
        toolchain_identity=toolchain_identity,
    )


def _normalize_benchmark_id(path: str, marker: str) -> str:
    if marker not in path:
        raise ContractError(f"benchmark path lacks identity marker {marker!r}: {path}")
    benchmark_id = path.split(marker, 1)[1]
    parts = benchmark_id.split("/")
    if not benchmark_id or any(part in {"", ".", ".."} for part in parts):
        raise ContractError(f"unsafe normalized benchmark identity: {benchmark_id!r}")
    return benchmark_id


def _selected_paths(file_list: Path) -> list[str]:
    try:
        lines = file_list.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError) as exc:
        raise ContractError(f"cannot read selected list: {file_list}") from exc
    if not lines or any(not line for line in lines):
        raise ContractError("selected list must be nonempty with no blank lines")
    for raw_path in lines:
        path = Path(raw_path)
        if not path.is_absolute() or not path.is_file():
            raise ContractError(
                f"benchmark path must be an existing absolute file: {raw_path}"
            )
    return lines


def _official_benchmark_id(value: object) -> str:
    if not isinstance(value, str) or "\\" in value:
        raise ContractError(f"invalid official benchmark identity: {value!r}")
    parts = value.split("/")
    if (
        len(parts) < 4
        or parts[0] != "non-incremental"
        or any(part in {"", ".", ".."} for part in parts)
    ):
        raise ContractError(f"invalid official benchmark identity: {value!r}")
    return value


def _official_selected(path: Path) -> tuple[bytes, list[str]]:
    if path.is_symlink() or not path.is_file():
        raise ContractError(f"official selected list is not a regular file: {path}")
    raw = path.read_bytes()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ContractError("official selected list is not UTF-8") from exc
    if not text.endswith("\n") or "\r" in text:
        raise ContractError("official selected list is not canonically LF-terminated")
    selected = text.splitlines()
    if not selected:
        raise ContractError("official selected list is empty")
    previous: str | None = None
    for benchmark_id in selected:
        _official_benchmark_id(benchmark_id)
        if previous is not None and benchmark_id <= previous:
            raise ContractError("official selected list is not strictly sorted and unique")
        previous = benchmark_id
    return raw, selected


def _canonical_jsonl_row(raw: bytes, label: str) -> dict[str, Any]:
    try:
        row = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError(f"malformed selected-file ledger row: {label}") from exc
    if not isinstance(row, dict) or raw != canonical_bytes(row):
        raise ContractError(f"non-canonical selected-file ledger row: {label}")
    return row


def _official_selection_identity(
    accepted_root: Path,
) -> tuple[dict[str, Any], list[str]]:
    if accepted_root.is_symlink() or not accepted_root.is_dir():
        raise ContractError(
            f"official selection root is not a regular directory: {accepted_root}"
        )
    completion_path = accepted_root / "complete.json"
    if completion_path.is_symlink() or not completion_path.is_file():
        raise ContractError("official selection completion is not a regular file")
    completion = read_canonical_json(completion_path)
    expected_fields = {
        "artifacts",
        "authority_sha256",
        "metadata_rows",
        "payload_sha256",
        "schema",
        "selected_files",
        "selection_observed",
        "status",
    }
    if not isinstance(completion, dict) or set(completion) != expected_fields:
        raise ContractError("official selection completion field set mismatch")
    if (
        completion["schema"] != OFFICIAL_SELECTION_SCHEMA
        or completion["status"] != "complete"
        or completion["selection_observed"] is not True
        or not _is_sha256(completion["authority_sha256"])
        or not _is_sha256(completion["payload_sha256"])
    ):
        raise ContractError("official selection is not a completed observed selection")
    selected_count = completion["selected_files"]
    metadata_rows = completion["metadata_rows"]
    if (
        isinstance(selected_count, bool)
        or not isinstance(selected_count, int)
        or selected_count <= 0
        or isinstance(metadata_rows, bool)
        or not isinstance(metadata_rows, int)
        or metadata_rows < selected_count
    ):
        raise ContractError("official selection completion counts are invalid")
    payload = {key: value for key, value in completion.items() if key != "payload_sha256"}
    if completion["payload_sha256"] != digest(payload):
        raise ContractError("official selection completion payload hash mismatch")
    completion_sha256 = sha256_file(completion_path)
    if accepted_root.name != f"accepted-{completion_sha256}":
        raise ContractError("official selection content-addressed root mismatch")
    artifacts = completion["artifacts"]
    if not isinstance(artifacts, dict):
        raise ContractError("official selection artifact map is invalid")
    selected_path = accepted_root / "official-selected.txt"
    ledger_path = accepted_root / "selected-files.jsonl"
    for name, path in (
        ("official-selected.txt", selected_path),
        ("selected-files.jsonl", ledger_path),
    ):
        expected = artifacts.get(name)
        if (
            not _is_sha256(expected)
            or path.is_symlink()
            or not path.is_file()
            or sha256_file(path) != expected
        ):
            raise ContractError(f"official selection artifact identity mismatch: {name}")
    selected_raw, selected = _official_selected(selected_path)
    if len(selected) != selected_count:
        raise ContractError("official selection count differs from selected list")
    identity = {
        "completion_payload_sha256": completion["payload_sha256"],
        "completion_sha256": completion_sha256,
        "official_selected": {
            "bytes": len(selected_raw),
            "sha256": artifacts["official-selected.txt"],
        },
        "selected_files": {
            "bytes": ledger_path.stat().st_size,
            "rows": selected_count,
            "sha256": artifacts["selected-files.jsonl"],
        },
    }
    return identity, selected


def selection_input_manifest(file_list: Path, marker: str) -> dict[str, Any]:
    """Freeze the exact ordered benchmark IDs and bytes used by E1b preflight."""

    benchmarks = []
    seen_ids: set[str] = set()
    for sequence, raw_path in enumerate(_selected_paths(file_list)):
        benchmark_id = _normalize_benchmark_id(raw_path, marker)
        if benchmark_id in seen_ids:
            raise ContractError(f"duplicate benchmark identity: {benchmark_id}")
        seen_ids.add(benchmark_id)
        path = Path(raw_path)
        benchmarks.append(
            {
                "sequence": sequence,
                "path": raw_path,
                "benchmark_id": benchmark_id,
                "benchmark_sha256": sha256_file(path),
                "input_bytes": path.stat().st_size,
            }
        )
    return {
        "schema": SELECTION_INPUT_SCHEMA,
        "selected_list_sha256": sha256_file(file_list),
        "benchmark_id_marker": marker,
        "benchmarks": benchmarks,
    }


def official_selection_input_manifest(
    file_list: Path, marker: str, accepted_root: Path
) -> dict[str, Any]:
    """Bind an E1b execution ledger to one accepted S4 selection artifact."""

    if marker != "non-incremental/":
        raise ContractError("official selection requires the canonical benchmark marker")
    selection_identity, official_selected = _official_selection_identity(accepted_root)
    paths = _selected_paths(file_list)
    requested = []
    previous_official_id: str | None = None
    for raw_path in paths:
        benchmark_id = _normalize_benchmark_id(raw_path, marker)
        official_id = f"{marker}{benchmark_id}"
        _official_benchmark_id(official_id)
        if previous_official_id is not None and official_id <= previous_official_id:
            raise ContractError(
                "execution list is not a strictly ordered official-selection subset"
            )
        previous_official_id = official_id
        requested.append((raw_path, benchmark_id, official_id))
    ledger_path = accepted_root / "selected-files.jsonl"
    benchmarks = []
    requested_index = 0
    with ledger_path.open("rb") as ledger:
        for ledger_index, official_id in enumerate(official_selected):
            raw_row = ledger.readline()
            if not raw_row:
                raise ContractError("selected-file ledger ended before official selected list")
            row = _canonical_jsonl_row(raw_row, str(ledger_index))
            if set(row) != {"archive", "benchmark_id", "bytes", "logic", "sha256"}:
                raise ContractError(
                    f"selected-file ledger field set mismatch: {ledger_index}"
                )
            expected_logic = official_id.split("/", 2)[1]
            expected_sha256 = row.get("sha256")
            expected_bytes = row.get("bytes")
            if (
                row.get("benchmark_id") != official_id
                or row.get("logic") != expected_logic
                or not isinstance(row.get("archive"), str)
                or isinstance(expected_bytes, bool)
                or not isinstance(expected_bytes, int)
                or expected_bytes < 0
                or not _is_sha256(expected_sha256)
            ):
                raise ContractError(
                    f"selected-file ledger identity mismatch: {ledger_index}"
                )
            if requested_index >= len(requested):
                continue
            raw_path, benchmark_id, requested_official_id = requested[requested_index]
            if requested_official_id < official_id:
                raise ContractError(
                    f"execution benchmark is not officially selected: {requested_official_id}"
                )
            if requested_official_id != official_id:
                continue
            path = Path(raw_path)
            if path.is_symlink() or not path.is_file():
                raise ContractError(f"official benchmark is not a regular file: {raw_path}")
            if (
                path.stat().st_size != expected_bytes
                or sha256_file(path) != expected_sha256
            ):
                raise ContractError(f"official benchmark bytes differ: {benchmark_id}")
            benchmarks.append(
                {
                    "sequence": requested_index,
                    "path": raw_path,
                    "benchmark_id": benchmark_id,
                    "benchmark_sha256": expected_sha256,
                    "input_bytes": expected_bytes,
                }
            )
            requested_index += 1
        if ledger.readline():
            raise ContractError("selected-file ledger has rows beyond official selected list")
    if requested_index != len(requested):
        missing = requested[requested_index][2]
        raise ContractError(f"execution benchmark is not officially selected: {missing}")
    return {
        "schema": OFFICIAL_SELECTION_INPUT_SCHEMA,
        "selected_list_sha256": sha256_file(file_list),
        "benchmark_id_marker": marker,
        "official_selection": selection_identity,
        "benchmarks": benchmarks,
    }


def load_benchmark_inputs(
    file_list: Path,
    *,
    selection_manifest: Path,
    marker: str,
    solver_config_sha256: str,
    official_selection_root: Path | None = None,
) -> list[BenchmarkInput]:
    lines = _selected_paths(file_list)
    observed_selection = read_canonical_json(selection_manifest)
    if not isinstance(observed_selection, dict):
        raise ContractError("selection manifest is not an object")
    if observed_selection.get("schema") == OFFICIAL_SELECTION_INPUT_SCHEMA:
        if official_selection_root is None:
            raise ContractError("official selection preflight requires its accepted root")
        expected_selection = official_selection_input_manifest(
            file_list, marker, official_selection_root
        )
    elif observed_selection.get("schema") == SELECTION_INPUT_SCHEMA:
        if official_selection_root is not None:
            raise ContractError("accepted selection root requires an admitted selection manifest")
        expected_selection = selection_input_manifest(file_list, marker)
    else:
        raise ContractError("selection manifest schema mismatch")
    if observed_selection != expected_selection:
        raise ContractError("selection manifest benchmark identity mismatch")
    inputs = []
    seen_ids: set[str] = set()
    seen_keys: set[str] = set()
    for sequence, raw_path in enumerate(lines):
        path = Path(raw_path)
        benchmark_id = _normalize_benchmark_id(raw_path, marker)
        benchmark_sha256 = sha256_file(path)
        key = result_key(benchmark_id, benchmark_sha256, solver_config_sha256)
        if benchmark_id in seen_ids or key in seen_keys:
            raise ContractError(f"duplicate benchmark identity in selected list: {benchmark_id}")
        seen_ids.add(benchmark_id)
        seen_keys.add(key)
        meta = read_meta(raw_path)
        inputs.append(
            BenchmarkInput(
                sequence=sequence,
                path=raw_path,
                benchmark_id=benchmark_id,
                benchmark_sha256=benchmark_sha256,
                input_bytes=path.stat().st_size,
                result_key=key,
                logic=meta.logic or "UNKNOWN",
                expected_status=meta.status.value if meta.status else None,
                num_named_assertions=meta.num_named,
            )
        )
    return inputs


def _assignments(inputs: list[BenchmarkInput], shard_count: int) -> list[dict[str, Any]]:
    return [
        {
            "shard_id": str(shard),
            "result_keys": [
                row.result_key for row in inputs if row.sequence % shard_count == shard
            ],
        }
        for shard in range(shard_count)
    ]


def _validate_preflight(
    *,
    run: dict[str, Any],
    repository_root: Path,
    source_root: Path,
    file_list: Path,
    selection_manifest: Path,
    corpus_manifest: Path,
    environment_manifest: Path,
    solver_id: str,
    command_template: list[str],
    track: str,
    wall_limit_ms: int,
    memory_limit_bytes: int,
    cores: int,
    shard_index: int | None,
    shard_count: int,
    resource_session_id: str | None,
    require_active_enforcement: bool,
    source_identity: dict[str, Any] | None,
    official_selection_root: Path | None,
    allow_unadmitted_selection_fixture: bool,
    solver_environment: dict[str, str] | None,
) -> tuple[dict[str, Any], str]:
    identity, run_hash = validate_run(run)
    enforcement = validate_enforcement(run)
    selection = read_canonical_json(selection_manifest)
    selection_schema = selection.get("schema") if isinstance(selection, dict) else None
    if selection_schema == OFFICIAL_SELECTION_INPUT_SCHEMA:
        if official_selection_root is None:
            raise ContractError("admitted selection preflight requires --official-selection-root")
    elif selection_schema == SELECTION_INPUT_SCHEMA:
        if official_selection_root is not None:
            raise ContractError("legacy selection manifest cannot name an official selection root")
        if (
            enforcement["kind"] != FIXTURE_KIND
            and not allow_unadmitted_selection_fixture
        ):
            raise ContractError(
                "cgroup-backed preflight rejects an unadmitted selection fixture"
            )
    else:
        raise ContractError("selection manifest schema mismatch")
    source = (
        source_identity_artifact(repository_root, source_root)
        if source_identity is None
        else validate_source_identity(source_identity, source_root)
    )
    checks = {
        "selection_manifest_sha256": sha256_file(selection_manifest),
        "selected_list_sha256": sha256_file(file_list),
        "corpus_identity_sha256": sha256_file(corpus_manifest),
        "solver_binary_sha256": sha256_file(_solver_binary(command_template)),
        "solver_command_sha256": solver_command_sha256(command_template),
        "solver_environment_sha256": digest(
            normalize_solver_environment(solver_environment)
        ),
        "runner_source_sha256": source["runner_source_sha256"],
        "source_tree_state_sha256": source["source_tree_state_sha256"],
        "toolchain_identity_sha256": toolchain_identity_sha256(),
        "environment_class_sha256": sha256_file(environment_manifest),
        "resource_enforcement_sha256": digest(enforcement),
        "resource_policy_sha256": digest(resource_policy_for(enforcement)),
        "output_capture_policy_sha256": digest(OUTPUT_CAPTURE_POLICY),
    }
    for field, observed in checks.items():
        if identity[field] != observed:
            raise ContractError(f"preflight identity mismatch: {field}")
    scalar_checks = {
        "solver_id": solver_id,
        "repository_commit": source["repository_commit"],
        "track": track,
        "wall_limit_ms": wall_limit_ms,
        "cpu_limit_ms": wall_limit_ms * cores,
        "memory_limit_bytes": memory_limit_bytes,
        "cores": cores,
        "shard_count": shard_count,
        "shard_mapping": "striped-index-v1",
        "verdict_policy": VERDICT_POLICY,
    }
    for field, observed in scalar_checks.items():
        if identity[field] != observed:
            raise ContractError(f"preflight identity mismatch: {field}")
    if shard_index is not None and not 0 <= shard_index < shard_count:
        raise ContractError("shard index is outside the registered shard count")
    if enforcement["kind"] == FIXTURE_KIND:
        if resource_session_id is not None:
            raise ContractError("fixture execution cannot name a resource session")
    elif enforcement["kind"] in {CGROUP_KIND, MULTI_HOST_KIND}:
        if require_active_enforcement:
            if resource_session_id is None:
                raise ContractError("E2 shard execution requires a resource session")
            validate_snapshot(
                cgroup_snapshot(), enforcement, session_id=resource_session_id
            )
    else:
        raise ContractError("unsupported aggregate resource enforcement")
    return identity, run_hash


def preflight_resumable(
    *,
    run_manifest: Path,
    repository_root: Path,
    source_root: Path,
    file_list: Path,
    selection_manifest: Path,
    corpus_manifest: Path,
    environment_manifest: Path,
    solver_id: str,
    command_template: list[str],
    track: str,
    wall_limit_ms: int,
    memory_limit_bytes: int,
    cores: int,
    shard_index: int | None,
    shard_count: int,
    benchmark_id_marker: str,
    resource_session_id: str | None = None,
    require_active_enforcement: bool = False,
    source_identity_manifest: Path | None = None,
    official_selection_root: Path | None = None,
    allow_unadmitted_selection_fixture: bool = False,
    solver_environment: dict[str, str] | None = None,
) -> tuple[dict[str, Any], dict[str, Any], str, list[BenchmarkInput]]:
    """Validate all immutable inputs without creating the run directory."""

    run = read_canonical_json(run_manifest)
    source_identity = (
        read_canonical_json(source_identity_manifest)
        if source_identity_manifest is not None
        else None
    )
    identity, run_hash = _validate_preflight(
        run=run,
        repository_root=repository_root,
        source_root=source_root,
        file_list=file_list,
        selection_manifest=selection_manifest,
        corpus_manifest=corpus_manifest,
        environment_manifest=environment_manifest,
        solver_id=solver_id,
        command_template=command_template,
        track=track,
        wall_limit_ms=wall_limit_ms,
        memory_limit_bytes=memory_limit_bytes,
        cores=cores,
        shard_index=shard_index,
        shard_count=shard_count,
        resource_session_id=resource_session_id,
        require_active_enforcement=require_active_enforcement,
        source_identity=source_identity,
        official_selection_root=official_selection_root,
        allow_unadmitted_selection_fixture=allow_unadmitted_selection_fixture,
        solver_environment=solver_environment,
    )
    inputs = load_benchmark_inputs(
        file_list,
        selection_manifest=selection_manifest,
        marker=benchmark_id_marker,
        solver_config_sha256=identity["solver_config_sha256"],
        official_selection_root=official_selection_root,
    )
    return run, identity, run_hash, inputs


def _selection_artifact(
    run_hash: str, selected_list_sha256: str, marker: str, inputs: list[BenchmarkInput]
) -> dict[str, Any]:
    return {
        "schema": SELECTION_SCHEMA,
        "run_identity_sha256": run_hash,
        "selected_list_sha256": selected_list_sha256,
        "benchmark_id_marker": marker,
        "benchmarks": [row.artifact() for row in inputs],
    }


def _load_records(run_dir: Path) -> list[dict[str, Any]]:
    records_dir = run_dir / "records"
    if not records_dir.exists():
        return []
    records = []
    for path in sorted(records_dir.iterdir(), key=lambda item: item.name):
        if not path.is_file() or path.suffix != ".json":
            raise ContractError(f"unexpected result artifact: {path}")
        record = read_canonical_json(path)
        if path.name != f"{record.get('result_key')}.json":
            raise ContractError(f"record filename/key mismatch: {path}")
        records.append(record)
    return records


def _verify_record_input(
    record: dict[str, Any],
    row: BenchmarkInput,
    identity: dict[str, Any],
    run_hash: str,
    run_dir: Path,
) -> None:
    validate_record(record, run_hash, identity)
    expected = {
        "result_key": row.result_key,
        "benchmark_id": row.benchmark_id,
        "benchmark_sha256": row.benchmark_sha256,
        "sequence": row.sequence,
        "expected_status": row.expected_status,
    }
    for field, value in expected.items():
        if record[field] != value:
            raise ContractError(f"existing result/input mismatch: {field}")
    for stream in ("stdout", "stderr"):
        sidecar = run_dir / "outputs" / stream / f"{record[f'{stream}_sha256']}.bin"
        try:
            data = sidecar.read_bytes()
        except OSError as exc:
            raise ContractError(f"missing {stream} sidecar for existing result") from exc
        if sha256_bytes(data) != record[f"{stream}_sha256"]:
            raise ContractError(f"{stream} sidecar hash mismatch for existing result")
        if len(data) != record[f"{stream}_bytes"]:
            raise ContractError(f"{stream} sidecar size mismatch for existing result")


def _install_sidecar(run_dir: Path, stream: str, data: bytes) -> tuple[str, int]:
    digest_hex = sha256_bytes(data)
    atomic_install_bytes(
        run_dir / "outputs" / stream,
        f"{digest_hex}.bin",
        data,
        quarantine_root=run_dir / "quarantine",
    )
    return digest_hex, len(data)


def _result_record(
    *,
    row: BenchmarkInput,
    run_result: RunResult,
    identity: dict[str, Any],
    run_hash: str,
    shard_id: str,
    attempt_id: str,
    stdout_sha256: str,
    stdout_bytes: int,
    stderr_sha256: str,
    stderr_bytes: int,
) -> dict[str, Any]:
    observed = run_result.observed.value if run_result.observed else None
    wall_time_ns = (
        identity["wall_limit_ms"] * 1_000_000
        if run_result.termination_class == "wall-timeout"
        else round(run_result.scoring_wall_time * 1_000_000_000)
    )
    return seal_record(
        {
            "schema": RESULT_SCHEMA,
            "run_identity_sha256": run_hash,
            "result_key": row.result_key,
            "benchmark_id": row.benchmark_id,
            "benchmark_sha256": row.benchmark_sha256,
            "solver_id": identity["solver_id"],
            "solver_config_sha256": identity["solver_config_sha256"],
            "shard_id": shard_id,
            "sequence": row.sequence,
            "attempt_id": attempt_id,
            "environment_class_sha256": identity["environment_class_sha256"],
            "expected_status": row.expected_status,
            "observed_status": observed,
            "reported_status": observed,
            "verdict_admission": "admitted" if observed is not None else "no-verdict",
            "termination_class": run_result.termination_class,
            "exit_code": run_result.exit_code,
            "signal": run_result.signal,
            "resource_limit_kind": run_result.resource_limit_kind,
            "wall_time_ns": wall_time_ns,
            "runner_elapsed_ns": max(
                wall_time_ns, round(run_result.runner_elapsed * 1_000_000_000)
            ),
            "cpu_time_ns": round(run_result.cpu_time * 1_000_000_000),
            "peak_rss_bytes": run_result.peak_rss_bytes,
            "stdout_sha256": stdout_sha256,
            "stdout_bytes": stdout_bytes,
            "stderr_sha256": stderr_sha256,
            "stderr_bytes": stderr_bytes,
        }
    )


def _attempts_for_shard(run_dir: Path, shard_id: str) -> list[dict[str, Any]]:
    directory = run_dir / "attempts" / shard_id
    if not directory.is_dir():
        return []
    terminals = run_dir / "terminals" / shard_id
    attempts = []
    for path in sorted(directory.iterdir(), key=lambda item: item.name):
        attempt = read_canonical_json(path)
        terminal_path = terminals / f"{attempt['attempt_id']}.json"
        if terminal_path.exists():
            if attempt["terminal"] is not None:
                raise ContractError(f"duplicate embedded/separate terminal: {terminal_path}")
            attempt["terminal"] = read_canonical_json(terminal_path)
        attempts.append(attempt)
    return attempts


def _terminal(
    *,
    status: str,
    assigned: set[str],
    records: list[dict[str, Any]],
    new_keys: set[str],
    skipped_keys: set[str],
    started_ns: int,
) -> dict[str, Any]:
    durable = {record["result_key"] for record in records}
    missing = assigned - durable
    return {
        "status": status,
        "exit_code": 0 if status == "completed" else 1,
        "signal": None,
        "wall_time_ns": max(0, time.time_ns() - started_ns),
        "peak_rss_bytes": max(
            (record["peak_rss_bytes"] for record in records), default=0
        ),
        "completed_count": len(durable),
        "result_set_sha256": record_set_sha256(records),
        "durable_result_keys": sorted(durable),
        "new_result_keys": sorted(new_keys),
        "skipped_result_keys": sorted(skipped_keys),
        "missing_result_keys": sorted(missing),
        "ended_at_ns": time.time_ns(),
    }


def _completion(
    run_hash: str,
    assigned: set[str],
    records: list[dict[str, Any]],
    attempts: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "state": "complete",
        "run_identity_sha256": run_hash,
        "assigned_count": len(assigned),
        "completed_count": len(records),
        "missing_result_keys": [],
        "result_set_sha256": record_set_sha256(records),
        "attempt_ids": sorted(attempt["attempt_id"] for attempt in attempts),
        "unclosed_attempt_ids": sorted(
            attempt["attempt_id"]
            for attempt in attempts
            if attempt["terminal"] is None
        ),
    }


def _execute_one(
    command_template: list[str],
    row: BenchmarkInput,
    wall_limit_s: float,
    memory_limit_bytes: int,
    runner: Runner,
    solver_environment: dict[str, str],
) -> RunResult:
    command = [token.replace("{bench}", row.path) for token in command_template]
    environment = os.environ.copy()
    environment.update(solver_environment)
    return runner(
        command,
        wall_limit_s=wall_limit_s,
        mem_limit_bytes=memory_limit_bytes,
        env=environment,
    )


def _runner_error_result(exc: BaseException) -> RunResult:
    stderr = (f"runner-error: {type(exc).__name__}: {exc}\n").encode("utf-8")
    return RunResult(
        reported=None,
        observed=None,
        wall_time=0.0,
        scoring_wall_time=0.0,
        runner_elapsed=0.0,
        cpu_time=0.0,
        exit_code=None,
        signal=None,
        termination_class="runner-error",
        resource_limit_kind=None,
        timed_out=False,
        mem_exceeded=False,
        peak_rss_bytes=0,
        stdout="",
        stderr=stderr.decode("utf-8"),
        stdout_bytes=b"",
        stderr_bytes=stderr,
    )


def execute_resumable(
    *,
    run_manifest: Path,
    run_dir: Path,
    repository_root: Path,
    source_root: Path,
    file_list: Path,
    selection_manifest: Path,
    corpus_manifest: Path,
    environment_manifest: Path,
    solver_id: str,
    command_template: list[str],
    track: str,
    wall_limit_ms: int,
    memory_limit_bytes: int,
    cores: int,
    shard_index: int,
    shard_count: int,
    benchmark_id_marker: str,
    verbose: bool,
    resource_session_id: str | None = None,
    source_identity_manifest: Path | None = None,
    official_selection_root: Path | None = None,
    allow_unadmitted_selection_fixture: bool = False,
    runner: Runner = run_solver_metered,
    phase_hook: PhaseHook | None = None,
    solver_environment: dict[str, str] | None = None,
) -> bool:
    """Execute one resumable shard and return whether the whole run is complete."""

    run, identity, run_hash, inputs = preflight_resumable(
        run_manifest=run_manifest,
        repository_root=repository_root,
        source_root=source_root,
        file_list=file_list,
        selection_manifest=selection_manifest,
        corpus_manifest=corpus_manifest,
        environment_manifest=environment_manifest,
        solver_id=solver_id,
        command_template=command_template,
        track=track,
        wall_limit_ms=wall_limit_ms,
        memory_limit_bytes=memory_limit_bytes,
        cores=cores,
        shard_index=shard_index,
        shard_count=shard_count,
        benchmark_id_marker=benchmark_id_marker,
        resource_session_id=resource_session_id,
        require_active_enforcement=True,
        source_identity_manifest=source_identity_manifest,
        official_selection_root=official_selection_root,
        allow_unadmitted_selection_fixture=allow_unadmitted_selection_fixture,
        solver_environment=solver_environment,
    )
    assignments = _assignments(inputs, shard_count)
    normalized_solver_environment = normalize_solver_environment(solver_environment)
    shard_id = str(shard_index)
    shard_inputs = [row for row in inputs if row.sequence % shard_count == shard_index]
    assigned = {row.result_key for row in shard_inputs}
    quarantine = run_dir / "quarantine"

    atomic_install_json(run_dir, "run.json", run, quarantine_root=quarantine)
    atomic_install_json(
        run_dir,
        "selection.json",
        _selection_artifact(
            run_hash,
            identity["selected_list_sha256"],
            benchmark_id_marker,
            inputs,
        ),
        quarantine_root=quarantine,
    )
    for assignment in assignments:
        atomic_install_json(
            run_dir / "assignments",
            f"{assignment['shard_id']}.json",
            assignment,
            quarantine_root=quarantine,
        )

    completion_path = run_dir / "completions" / f"{shard_id}.json"
    if completion_path.exists():
        # A completed shard is immutable. Validate all available state instead
        # of creating a redundant attempt.
        complete = all(
            (run_dir / "completions" / f"{index}.json").exists()
            for index in range(shard_count)
        )
        if complete:
            validate_bundle_directory(
                run_dir,
                require_output_sidecars=True,
                require_resource_evidence=run["resource_enforcement"]["kind"]
                == FIXTURE_KIND,
                require_multi_host_evidence=False,
            )
        return complete

    owner_id = f"{shard_id}-{os.getpid()}-{uuid.uuid4().hex}"
    lease = acquire_shard_lease(
        run_dir,
        shard_id,
        {
            "owner_id": owner_id,
            "run_identity_sha256": run_hash,
            "shard_id": shard_id,
            "host_id": socket.gethostname(),
            "pid": os.getpid(),
            "acquired_at_ns": time.time_ns(),
        },
    )
    attempt_id = f"{shard_id}-{time.time_ns()}-{uuid.uuid4().hex}"
    started_ns = time.time_ns()
    launch = {
        "attempt_id": attempt_id,
        "run_identity_sha256": run_hash,
        "shard_id": shard_id,
        "host_id": socket.gethostname(),
        "pid": os.getpid(),
        "assigned_count": len(assigned),
        "launched_at_ns": started_ns,
        "enforcement_id": run["resource_enforcement"]["enforcement_id"],
        "resource_session_id": resource_session_id,
        "environment_class_sha256": identity["environment_class_sha256"],
        "terminal": None,
    }
    new_keys: set[str] = set()
    skipped_keys: set[str] = set()
    terminal_written = False
    try:
        recover_orphan_temporaries(run_dir / "records", quarantine_root=quarantine)
        atomic_install_json(
            run_dir / "attempts" / shard_id,
            f"{attempt_id}.json",
            launch,
            quarantine_root=quarantine,
        )
        if phase_hook is not None:
            phase_hook("before_solver_start")
        existing = {record["result_key"]: record for record in _load_records(run_dir)}
        for row in shard_inputs:
            record = existing.get(row.result_key)
            if record is not None:
                _verify_record_input(record, row, identity, run_hash, run_dir)
                skipped_keys.add(row.result_key)
                continue
            try:
                run_result = _execute_one(
                    command_template,
                    row,
                    wall_limit_ms / 1000.0,
                    memory_limit_bytes,
                    runner,
                    normalized_solver_environment,
                )
            except Exception as exc:
                run_result = _runner_error_result(exc)
            stdout_sha256, stdout_bytes = _install_sidecar(
                run_dir, "stdout", run_result.stdout_bytes
            )
            stderr_sha256, stderr_bytes = _install_sidecar(
                run_dir, "stderr", run_result.stderr_bytes
            )
            record = _result_record(
                row=row,
                run_result=run_result,
                identity=identity,
                run_hash=run_hash,
                shard_id=shard_id,
                attempt_id=attempt_id,
                stdout_sha256=stdout_sha256,
                stdout_bytes=stdout_bytes,
                stderr_sha256=stderr_sha256,
                stderr_bytes=stderr_bytes,
            )
            validate_record(record, run_hash, identity)
            atomic_install_json(
                run_dir / "records",
                f"{row.result_key}.json",
                record,
                quarantine_root=quarantine,
            )
            existing[row.result_key] = record
            new_keys.add(row.result_key)
            if verbose:
                observed = record["observed_status"] or "none"
                print(
                    f"RESUME|shard={shard_id}|sequence={row.sequence}|"
                    f"status={observed}|termination={record['termination_class']}",
                    file=sys.stderr,
                )

        records = [existing[key] for key in sorted(assigned)]
        terminal = _terminal(
            status="completed",
            assigned=assigned,
            records=records,
            new_keys=new_keys,
            skipped_keys=skipped_keys,
            started_ns=started_ns,
        )
        atomic_install_json(
            run_dir / "terminals" / shard_id,
            f"{attempt_id}.json",
            terminal,
            quarantine_root=quarantine,
        )
        terminal_written = True
        attempts = _attempts_for_shard(run_dir, shard_id)
        atomic_install_json(
            run_dir / "completions",
            f"{shard_id}.json",
            _completion(run_hash, assigned, records, attempts),
            quarantine_root=quarantine,
        )
    except BaseException:
        if not terminal_written:
            try:
                records = [
                    record
                    for record in _load_records(run_dir)
                    if record.get("result_key") in assigned
                ]
                atomic_install_json(
                    run_dir / "terminals" / shard_id,
                    f"{attempt_id}.json",
                    _terminal(
                        status="failed",
                        assigned=assigned,
                        records=records,
                        new_keys=new_keys,
                        skipped_keys=skipped_keys,
                        started_ns=started_ns,
                    ),
                    quarantine_root=quarantine,
                )
            except Exception:
                pass
        raise
    finally:
        release_shard_lease(lease)

    complete = all(
        (run_dir / "completions" / f"{index}.json").exists()
        for index in range(shard_count)
    )
    if complete:
        validate_bundle_directory(
            run_dir,
            require_output_sidecars=True,
            require_resource_evidence=run["resource_enforcement"]["kind"]
            == FIXTURE_KIND,
            require_multi_host_evidence=False,
        )
    return complete


def export_legacy_raw(run_dir: Path, destination: Path) -> None:
    """Export current raw scoring JSON only from a complete, sidecar-valid run."""

    validate_bundle_directory(run_dir, require_output_sidecars=True)
    bundle = load_bundle(run_dir)
    verify_output_sidecars(run_dir, bundle.records)
    selection = read_canonical_json(run_dir / "selection.json")
    if selection.get("schema") != SELECTION_SCHEMA:
        raise ContractError("selection artifact schema mismatch")
    by_key = {row["result_key"]: row for row in selection["benchmarks"]}
    if set(by_key) != {record["result_key"] for record in bundle.records}:
        raise ContractError("selection/result population mismatch")
    raw: dict[str, dict[str, Any]] = {}
    solver_id = bundle.run["identity"]["solver_id"]
    for record in sorted(bundle.records, key=lambda value: value["sequence"]):
        source = by_key[record["result_key"]]
        raw[source["path"]] = {
            solver_id: {
                "solver": solver_id,
                "benchmark": source["path"],
                "division": source["logic"],
                "logic": source["logic"],
                "expected_status": record["expected_status"],
                "reported_status": record["reported_status"],
                "wall_time": record["wall_time_ns"] / 1_000_000_000,
                "cpu_time": record["cpu_time_ns"] / 1_000_000_000,
                "num_named_assertions": source["num_named_assertions"],
            }
        }
    data = json.dumps(raw, indent=2).encode("utf-8")
    atomic_install_bytes(destination.parent, destination.name, data)


__all__ = [
    "LeaseConflict",
    "cgroup_run_manifest",
    "execute_resumable",
    "export_legacy_raw",
    "fixture_run_manifest",
    "official_selection_input_manifest",
    "normalize_solver_environment",
    "preflight_resumable",
    "selection_input_manifest",
    "source_identity_artifact",
    "validate_source_identity",
]
