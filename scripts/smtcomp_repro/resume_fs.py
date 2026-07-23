"""Filesystem prototype for ADR-0344's immutable benchmark checkpoints.

The module uses a same-directory temporary file, fsync, and a no-replace hard
link as the commit point.  It is Linux-oriented E1 prototype code, not the
production remote launcher and not a claim about NFS or power-loss behavior.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import socket
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable

from resume_contract import Bundle, ContractError, canonical_bytes, merge_complete


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


def _json_files(directory: Path) -> list[Path]:
    if not directory.is_dir():
        raise ContractError(f"missing artifact directory: {directory}")
    entries = sorted(directory.iterdir(), key=lambda item: item.name)
    invalid = [
        path
        for path in entries
        if path.is_symlink() or not path.is_file() or path.suffix != ".json"
    ]
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
        "terminals",
        "outputs",
        "selection.json",
        "leases",
        "quarantine",
        "resource-sessions",
        "resource-completion.json",
        "multi-host-plan.json",
        "multi-host-commands",
        "multi-host-attempts",
        "multi-host-terminals",
        "multi-host-outputs",
        "multi-host-recoveries",
        "multi-host-fault.json",
        "multi-host-completion.json",
        "full-schedule.json",
        "full-wave-checkpoints",
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

    terminals_root = root / "terminals"
    if terminals_root.exists():
        terminal_shards = {path.name for path in terminals_root.iterdir()}
        if not terminal_shards <= set(attempts):
            raise ContractError("terminal shard has no attempt assignment")
        for shard_dir in sorted(terminals_root.iterdir(), key=lambda item: item.name):
            if not shard_dir.is_dir():
                raise ContractError(f"unexpected terminal artifact: {shard_dir.name}")
            by_id = {attempt["attempt_id"]: attempt for attempt in attempts[shard_dir.name]}
            for path in _json_files(shard_dir):
                attempt_id = path.stem
                attempt = by_id.get(attempt_id)
                if attempt is None:
                    raise ContractError(f"terminal has no launch manifest: {path}")
                if attempt["terminal"] is not None:
                    raise ContractError(f"duplicate embedded/separate terminal: {path}")
                attempt["terminal"] = _read_canonical_json(path)

    completions = {}
    for path in _json_files(root / "completions"):
        completions[path.stem] = _read_canonical_json(path)
    return Bundle(run, assignments, records, attempts, completions)


def verify_output_sidecars(root: Path, records: list[dict[str, Any]]) -> None:
    """Verify exact stdout/stderr sidecars before any scoring export."""

    for stream in ("stdout", "stderr"):
        directory = root / "outputs" / stream
        if not directory.is_dir():
            raise ContractError(f"missing output sidecar directory: {directory}")
        expected = {record[f"{stream}_sha256"] for record in records}
        present = {
            path.stem
            for path in directory.iterdir()
            if not path.is_symlink() and path.is_file() and path.suffix == ".bin"
        }
        invalid = [
            path.name
            for path in directory.iterdir()
            if path.is_symlink() or not path.is_file() or path.suffix != ".bin"
        ]
        if invalid:
            raise ContractError(f"unexpected output sidecar: {sorted(invalid)[0]}")
        if not expected <= present:
            raise ContractError(f"{stream} sidecar population mismatch")
        for digest_hex in sorted(expected):
            data = (directory / f"{digest_hex}.bin").read_bytes()
            if hashlib.sha256(data).hexdigest() != digest_hex:
                raise ContractError(f"{stream} sidecar hash mismatch")
            sizes = {
                record[f"{stream}_bytes"]
                for record in records
                if record[f"{stream}_sha256"] == digest_hex
            }
            if sizes != {len(data)}:
                raise ContractError(f"{stream} sidecar byte-count mismatch")


def validate_bundle_directory(
    root: Path,
    *,
    require_output_sidecars: bool = False,
    require_resource_evidence: bool = True,
    require_multi_host_evidence: bool = True,
) -> bytes:
    bundle = load_bundle(root)
    if require_output_sidecars:
        verify_output_sidecars(root, bundle.records)
    if require_resource_evidence:
        from resource_enforcement import validate_resource_evidence

        validate_resource_evidence(root, bundle)
    if require_multi_host_evidence:
        from resource_enforcement import MULTI_HOST_KIND

        if bundle.run.get("resource_enforcement", {}).get("kind") == MULTI_HOST_KIND:
            from multi_host import validate_multi_host_evidence

            validate_multi_host_evidence(root, bundle)
    return merge_complete(bundle)
