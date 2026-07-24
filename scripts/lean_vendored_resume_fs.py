"""Lean-owned immutable filesystem primitives.

This module vendors the small no-replace/fsync surface used by Lean execution
evidence.  It intentionally has no dependency on the SMT-COMP resume modules,
whose source identities and release cadence belong to a different lane.
"""

from __future__ import annotations

import json
import os
import re
import uuid
from pathlib import Path
from typing import Any, Callable


SAFE_LEAF = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*\Z")
PhaseHook = Callable[[str], None]


class LeanResumeFsError(ValueError):
    """A Lean checkpoint artifact violated the local filesystem contract."""


class CheckpointConflict(LeanResumeFsError):
    """The immutable destination exists with different bytes."""


def canonical_bytes(value: Any) -> bytes:
    """Encode one canonical JSON value with a terminating newline."""

    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def _safe_leaf(name: str) -> str:
    if not SAFE_LEAF.fullmatch(name) or name in {".", ".."}:
        raise LeanResumeFsError(f"unsafe artifact name: {name!r}")
    return name


def _fsync_directory(path: Path) -> None:
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    descriptor = os.open(path, flags)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _write_all(descriptor: int, data: bytes) -> None:
    offset = 0
    while offset < len(data):
        written = os.write(descriptor, data[offset:])
        if written <= 0:
            raise OSError("short write while installing checkpoint")
        offset += written


def _quarantine(
    path: Path,
    category: str,
    quarantine_root: Path | None = None,
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


def _atomic_install_bytes(
    directory: Path,
    filename: str,
    data: bytes,
    *,
    phase_hook: PhaseHook | None = None,
    quarantine_root: Path | None = None,
) -> str:
    filename = _safe_leaf(filename)
    directory.mkdir(parents=True, exist_ok=True)
    final = directory / filename
    temporary = directory / f".{filename}.tmp-{os.getpid()}-{uuid.uuid4().hex}"
    if phase_hook:
        phase_hook("before_temp_open")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0)
    descriptor = os.open(temporary, flags, 0o600)
    try:
        _write_all(descriptor, data)
        os.fsync(descriptor)
        if phase_hook:
            phase_hook("after_temp_fsync")

        try:
            os.link(temporary, final)
        except FileExistsError as exc:
            if final.read_bytes() == data:
                if final.stat().st_mode & 0o777 != 0o444:
                    final.chmod(0o444)
                    with final.open("rb") as existing:
                        os.fsync(existing.fileno())
                temporary.unlink()
                _fsync_directory(directory)
                return "existing-valid"
            conflict = _quarantine(temporary, "conflicts", quarantine_root)
            raise CheckpointConflict(
                f"immutable checkpoint conflict: {final}; incoming preserved at {conflict}"
            ) from exc

        os.fchmod(descriptor, 0o444)
        os.fsync(descriptor)
        if phase_hook:
            phase_hook("after_final_link")
    finally:
        os.close(descriptor)
    temporary.unlink()
    _fsync_directory(directory)
    if phase_hook:
        phase_hook("after_commit")
    return "installed"


def atomic_install_json(
    directory: Path,
    filename: str,
    value: Any,
    *,
    phase_hook: PhaseHook | None = None,
    quarantine_root: Path | None = None,
) -> str:
    """Install canonical JSON through an immutable no-overwrite boundary."""

    return _atomic_install_bytes(
        directory,
        filename,
        canonical_bytes(value),
        phase_hook=phase_hook,
        quarantine_root=quarantine_root,
    )


def atomic_install_bytes(
    directory: Path,
    filename: str,
    data: bytes,
    *,
    phase_hook: PhaseHook | None = None,
    quarantine_root: Path | None = None,
) -> str:
    """Install an exact-byte sidecar without replacing an existing object."""

    return _atomic_install_bytes(
        directory,
        filename,
        data,
        phase_hook=phase_hook,
        quarantine_root=quarantine_root,
    )


def recover_orphan_temporaries(
    directory: Path,
    *,
    quarantine_root: Path | None = None,
    eligible_targets: set[str] | None = None,
) -> list[Path]:
    """Quarantine, but never promote or delete, uncommitted temporary files."""

    if not directory.exists():
        return []
    recovered = []
    for path in sorted(directory.iterdir(), key=lambda item: item.name):
        target = None
        if path.name.startswith(".") and ".tmp-" in path.name:
            target = path.name[1:].split(".tmp-", 1)[0]
        if (
            path.is_file()
            and target
            and (eligible_targets is None or target in eligible_targets)
        ):
            recovered.append(_quarantine(path, "orphans", quarantine_root))
    return recovered


def read_canonical_json(path: Path) -> Any:
    """Read canonical JSON and reject malformed or non-canonical bytes."""

    try:
        raw = path.read_bytes()
        value = json.loads(raw)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise LeanResumeFsError(f"malformed artifact: {path}") from exc
    if raw != canonical_bytes(value):
        raise LeanResumeFsError(f"non-canonical artifact: {path}")
    return value
