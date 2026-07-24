"""Lane-neutral immutable filesystem primitives for ADR-0344 checkpoints.

The module uses a same-directory temporary file, fsync, and a no-replace hard
link as the commit point.  It is Linux-oriented E1 prototype code, not the
production remote launcher and not a claim about NFS or power-loss behavior.

Both lanes share this single source: the SMT lane imports it as a top-level
module (``smtcomp_repro`` is on ``sys.path``) and the Lean lane imports it as
``scripts.axeyum_fsprims`` (repository root on ``sys.path``).  The canonical
JSON encoder and the ``ContractError`` base come from the single authority
``resume_contract`` so there is exactly one definition of canonical bytes.
"""

from __future__ import annotations

import json
import os
import re
import socket
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable

try:
    from resume_contract import ContractError, canonical_bytes
except ModuleNotFoundError:
    import sys
    import pathlib

    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent / "smtcomp_repro"))
    from resume_contract import ContractError, canonical_bytes


SAFE_LEAF = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*\Z")
PhaseHook = Callable[[str], None]


class CheckpointConflict(ContractError):
    """The immutable destination exists with different bytes."""


class LeaseConflict(ContractError):
    """A shard already has a live or unrecovered owner lease."""


@dataclass(frozen=True)
class ShardLease:
    path: Path
    owner_id: str


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


def _atomic_install_bytes(
    directory: Path,
    filename: str,
    data: bytes,
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
    if phase_hook:
        phase_hook("before_temp_open")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0)
    # Keep the private temporary owner-writable through the hard-link commit.
    # Some NFS identity mappings expose the server-side owner UID rather than
    # the local credential; Linux protected-hardlink policy then rejects a link
    # after mode 0444 removes write permission. The final link is frozen through
    # the still-open descriptor before it is returned to any caller.
    fd = os.open(temp, flags, 0o600)
    try:
        _write_all(fd, data)
        os.fsync(fd)
        if phase_hook:
            phase_hook("after_temp_fsync")

        try:
            os.link(temp, final)
        except FileExistsError as exc:
            if final.read_bytes() == data:
                if final.stat().st_mode & 0o777 != 0o444:
                    final.chmod(0o444)
                    with final.open("rb") as existing:
                        os.fsync(existing.fileno())
                temp.unlink()
                _fsync_directory(directory)
                return "existing-valid"
            conflict = _quarantine(temp, "conflicts", quarantine_root)
            raise CheckpointConflict(
                f"immutable checkpoint conflict: {final}; incoming preserved at {conflict}"
            ) from exc

        os.fchmod(fd, 0o444)
        os.fsync(fd)
        if phase_hook:
            phase_hook("after_final_link")
    finally:
        os.close(fd)
    temp.unlink()
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
    """Install canonical JSON through the immutable no-overwrite boundary."""

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


def acquire_shard_lease(root: Path, shard_id: str, owner: dict[str, Any]) -> ShardLease:
    """Acquire a single-owner shard lease; an existing lease always fails closed."""

    shard_id = _safe_leaf(shard_id)
    owner_id = _safe_leaf(str(owner.get("owner_id", "")))
    if owner.get("host_id") != socket.gethostname() or owner.get("pid") != os.getpid():
        raise ContractError("lease owner does not describe the current process")
    lease_dir = root / "leases"
    path = lease_dir / f"{shard_id}.json"
    if path.exists():
        raise LeaseConflict(f"shard lease already exists: {path}")
    outcome = atomic_install_json(
        lease_dir,
        path.name,
        owner,
        quarantine_root=root / "quarantine",
    )
    if outcome != "installed":
        raise LeaseConflict(f"shard lease already exists: {path}")
    return ShardLease(path=path, owner_id=owner_id)


def release_shard_lease(lease: ShardLease) -> None:
    """Release only the lease still owned by this process."""

    owner = _read_canonical_json(lease.path)
    if owner.get("owner_id") != lease.owner_id:
        raise LeaseConflict(f"shard lease ownership changed: {lease.path}")
    lease.path.unlink()
    _fsync_directory(lease.path.parent)


def recover_shard_lease(
    root: Path,
    shard_id: str,
    expected_owner_id: str,
    *,
    recovery_id: str | None = None,
) -> Path:
    """Explicitly quarantine one exactly identified stale lease.

    The caller must first establish staleness out of band.  There is
    intentionally no age-based or automatic lease stealing.
    """

    path = root / "leases" / f"{_safe_leaf(shard_id)}.json"
    if recovery_id is not None:
        recovery_id = _safe_leaf(recovery_id)
        quarantine = root / "quarantine" / "stale-leases"
        destination = quarantine / f"{path.name}.{recovery_id}"
        if destination.exists():
            owner = _read_canonical_json(destination)
            if path.exists() or owner.get("owner_id") != expected_owner_id:
                raise LeaseConflict("stale-lease recovery replay mismatch")
            return destination
    owner = _read_canonical_json(path)
    if owner.get("owner_id") != expected_owner_id:
        raise LeaseConflict(f"stale-lease owner mismatch: {path}")
    if recovery_id is not None:
        quarantine.mkdir(parents=True, exist_ok=True)
        os.replace(path, destination)
        _fsync_directory(quarantine)
        _fsync_directory(quarantine.parent)
        _fsync_directory(path.parent)
        return destination
    return _quarantine(path, "stale-leases", root / "quarantine")


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


def _read_canonical_json(path: Path) -> Any:
    try:
        raw = path.read_bytes()
        value = json.loads(raw)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError(f"malformed artifact: {path}") from exc
    if raw != canonical_bytes(value):
        raise ContractError(f"non-canonical artifact: {path}")
    return value


def read_canonical_json(path: Path) -> Any:
    """Public fail-closed canonical JSON reader used by the production adapter."""

    return _read_canonical_json(path)
