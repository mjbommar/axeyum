"""Filesystem prototype for ADR-0344's immutable benchmark checkpoints.

The module uses a same-directory temporary file, fsync, and a no-replace hard
link as the commit point.  It is Linux-oriented E1 prototype code, not the
production remote launcher and not a claim about NFS or power-loss behavior.

The lane-neutral no-replace/fsync primitives now live in the shared
``axeyum_fsprims`` module; this file retains only the SMT-COMP bundle logic and
re-exports the shared surface so its importers are unaffected.
"""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path
from typing import Any

# The shared primitives live in ``scripts/axeyum_fsprims.py`` while this module
# lives in ``scripts/smtcomp_repro/``. SMT importers only place ``smtcomp_repro``
# on ``sys.path``, so add ``scripts`` before importing the shared module.
_SCRIPTS_DIR = Path(__file__).resolve().parent.parent
if str(_SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS_DIR))

from resume_contract import Bundle, ContractError, canonical_bytes, merge_complete

from axeyum_fsprims import (  # noqa: F401  (re-exported for resume_fs importers)
    CheckpointConflict,
    LeaseConflict,
    ShardLease,
    _read_canonical_json,
    _safe_leaf,
    acquire_shard_lease,
    atomic_install_bytes,
    atomic_install_json,
    read_canonical_json,
    recover_orphan_temporaries,
    recover_shard_lease,
    release_shard_lease,
)


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
