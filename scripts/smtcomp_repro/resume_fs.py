"""Filesystem prototype for ADR-0344's immutable benchmark checkpoints.

The module uses a same-directory temporary file, fsync, and a no-replace hard
link as the commit point.  It is Linux-oriented E1 prototype code, not the
production remote launcher and not a claim about NFS or power-loss behavior.
"""

from __future__ import annotations

import json
import os
import re
import uuid
from pathlib import Path
from typing import Any, Callable

from resume_contract import Bundle, ContractError, canonical_bytes, merge_complete


SAFE_LEAF = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*\Z")
PhaseHook = Callable[[str], None]


class CheckpointConflict(ContractError):
    """The immutable destination exists with different bytes."""


def _safe_leaf(name: str) -> str:
    if not SAFE_LEAF.fullmatch(name) or name in {".", ".."}:
        raise ContractError(f"unsafe artifact name: {name!r}")
    return name


def _fsync_directory(path: Path) -> None:
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    fd = os.open(path, flags)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _write_all(fd: int, data: bytes) -> None:
    offset = 0
    while offset < len(data):
        written = os.write(fd, data[offset:])
        if written <= 0:
            raise OSError("short write while installing checkpoint")
        offset += written


def _quarantine(
    path: Path, category: str, quarantine_root: Path | None = None
) -> Path:
    root = quarantine_root or path.parent.parent / "quarantine"
    quarantine = root / _safe_leaf(category)
    quarantine.mkdir(parents=True, exist_ok=True)
    destination = quarantine / f"{path.name}.{uuid.uuid4().hex}"
    os.replace(path, destination)
    _fsync_directory(quarantine)
    _fsync_directory(quarantine.parent)
    _fsync_directory(path.parent)
    return destination


def atomic_install_json(
    directory: Path,
    filename: str,
    value: Any,
    *,
    phase_hook: PhaseHook | None = None,
    quarantine_root: Path | None = None,
) -> str:
    """Install canonical JSON without overwriting an existing artifact.

    Returns ``installed`` for a new record and ``existing-valid`` when resume
    encounters the same immutable bytes. A different existing destination is
    preserved, the incoming temporary is quarantined, and the call fails.
    """

    filename = _safe_leaf(filename)
    directory.mkdir(parents=True, exist_ok=True)
    final = directory / filename
    temp = directory / f".{filename}.tmp-{os.getpid()}-{uuid.uuid4().hex}"
    data = canonical_bytes(value)

    if phase_hook:
        phase_hook("before_temp_open")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0)
    fd = os.open(temp, flags, 0o444)
    try:
        _write_all(fd, data)
        os.fchmod(fd, 0o444)
        os.fsync(fd)
    finally:
        os.close(fd)
    if phase_hook:
        phase_hook("after_temp_fsync")

    try:
        os.link(temp, final)
    except FileExistsError as exc:
        if final.read_bytes() == data:
            temp.unlink()
            _fsync_directory(directory)
            return "existing-valid"
        conflict = _quarantine(temp, "conflicts", quarantine_root)
        raise CheckpointConflict(
            f"immutable checkpoint conflict: {final}; incoming preserved at {conflict}"
        ) from exc

    if phase_hook:
        phase_hook("after_final_link")
    temp.unlink()
    _fsync_directory(directory)
    if phase_hook:
        phase_hook("after_commit")
    return "installed"


def recover_orphan_temporaries(
    directory: Path, *, quarantine_root: Path | None = None
) -> list[Path]:
    """Quarantine, but never promote or delete, uncommitted temporary files."""

    if not directory.exists():
        return []
    recovered = []
    for path in sorted(directory.iterdir(), key=lambda item: item.name):
        if path.is_file() and path.name.startswith(".") and ".tmp-" in path.name:
            recovered.append(_quarantine(path, "orphans", quarantine_root))
    return recovered


def _read_canonical_json(path: Path) -> Any:
    try:
        raw = path.read_bytes()
        value = json.loads(raw)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError(f"malformed artifact: {path}") from exc
    if raw != canonical_bytes(value):
        raise ContractError(f"non-canonical artifact: {path}")
    return value


def _json_files(directory: Path) -> list[Path]:
    if not directory.is_dir():
        raise ContractError(f"missing artifact directory: {directory}")
    entries = sorted(directory.iterdir(), key=lambda item: item.name)
    invalid = [path for path in entries if not path.is_file() or path.suffix != ".json"]
    if invalid:
        raise ContractError(f"unexpected artifact in {directory}: {invalid[0].name}")
    return entries


def materialize_bundle(
    root: Path,
    bundle: Bundle,
    *,
    include_records: bool = True,
) -> None:
    """Install a fixture bundle through the same immutable artifact boundary."""

    quarantine = root / "quarantine"
    atomic_install_json(root, "run.json", bundle.run, quarantine_root=quarantine)
    for assignment in bundle.assignments:
        shard = _safe_leaf(assignment["shard_id"])
        atomic_install_json(
            root / "assignments",
            f"{shard}.json",
            assignment,
            quarantine_root=quarantine,
        )
    for shard, attempts in bundle.attempts.items():
        shard = _safe_leaf(shard)
        for attempt in attempts:
            attempt_id = _safe_leaf(attempt["attempt_id"])
            atomic_install_json(
                root / "attempts" / shard,
                f"{attempt_id}.json",
                attempt,
                quarantine_root=quarantine,
            )
    if include_records:
        for record in bundle.records:
            atomic_install_json(
                root / "records",
                f"{record['result_key']}.json",
                record,
                quarantine_root=quarantine,
            )
    # Completion is deliberately installed last. A crash may leave an
    # incomplete namespace, but it must never publish completion first.
    for shard, completion in bundle.completions.items():
        shard = _safe_leaf(shard)
        atomic_install_json(
            root / "completions",
            f"{shard}.json",
            completion,
            quarantine_root=quarantine,
        )


def load_bundle(root: Path) -> Bundle:
    """Load only the exact accepted artifact namespace; quarantine is ignored."""

    allowed = {
        "run.json",
        "assignments",
        "attempts",
        "completions",
        "records",
        "quarantine",
    }
    if not root.is_dir():
        raise ContractError(f"missing run directory: {root}")
    unexpected = sorted(path.name for path in root.iterdir() if path.name not in allowed)
    if unexpected:
        raise ContractError(f"unexpected run artifact: {unexpected[0]}")

    run = _read_canonical_json(root / "run.json")
    assignment_paths = _json_files(root / "assignments")
    assignments = [_read_canonical_json(path) for path in assignment_paths]
    for path, assignment in zip(assignment_paths, assignments, strict=True):
        if path.name != f"{assignment.get('shard_id')}.json":
            raise ContractError(f"assignment filename/id mismatch: {path}")
    record_paths = _json_files(root / "records")
    records = [_read_canonical_json(path) for path in record_paths]
    for path, record in zip(record_paths, records, strict=True):
        if path.name != f"{record.get('result_key')}.json":
            raise ContractError(f"record filename/key mismatch: {path}")

    attempts_root = root / "attempts"
    if not attempts_root.is_dir():
        raise ContractError(f"missing artifact directory: {attempts_root}")
    attempts: dict[str, list[dict[str, Any]]] = {}
    for shard_dir in sorted(attempts_root.iterdir(), key=lambda item: item.name):
        if not shard_dir.is_dir():
            raise ContractError(f"unexpected attempt artifact: {shard_dir.name}")
        attempts[shard_dir.name] = [
            _read_canonical_json(path) for path in _json_files(shard_dir)
        ]
        for path, attempt in zip(
            _json_files(shard_dir), attempts[shard_dir.name], strict=True
        ):
            if path.name != f"{attempt.get('attempt_id')}.json":
                raise ContractError(f"attempt filename/id mismatch: {path}")

    completions = {}
    for path in _json_files(root / "completions"):
        completions[path.stem] = _read_canonical_json(path)
    return Bundle(run, assignments, records, attempts, completions)


def validate_bundle_directory(root: Path) -> bytes:
    return merge_complete(load_bundle(root))
