#!/usr/bin/env python3
"""Immutable local checkpoint-store controls for Lean parity TL0.7.3.

The store wraps the accepted ADR-0344 local no-replace primitive.  Its fixture
is synthetic and grants no Lean, U2, result-denominator, or parity credit.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from collections import Counter
from pathlib import Path
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SMTCOMP = ROOT / "scripts/smtcomp_repro"
sys.path.insert(0, str(SMTCOMP))

from resume_fs import (  # noqa: E402
    CheckpointConflict,
    atomic_install_json,
    recover_orphan_temporaries,
)


def _load_script(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


EVIDENCE_CONTRACT = _load_script(
    "lean_execution_evidence_for_store",
    ROOT / "scripts/gen-lean-execution-evidence.py",
)
WORKER = SMTCOMP / "resume_fs_fixture_worker.py"
PRIMITIVE = SMTCOMP / "resume_fs.py"
PREREGISTRATION_PLAN = (
    ROOT / "docs/plan/lean-execution-store-tl0.7.3-plan-2026-07-22.md"
)
RESULT_AUTHORITY = ROOT / "docs/plan/lean-execution-store-v1.json"
RESULT_JSON = ROOT / "docs/plan/generated/lean-execution-store.json"
RESULT_MARKDOWN = ROOT / "docs/plan/generated/lean-execution-store.md"
DEFAULT_EVIDENCE_ROOT = ROOT / "docs/plan/evidence/lean-execution-store-tl0.7.3"
STORE_SCHEMA = "axeyum-lean-execution-store-v1"
STORAGE_CLASSES_SCHEMA = "axeyum-lean-execution-storage-classes-v1"
CELL_SCHEMA = "axeyum-lean-execution-store-kill-cell-v1"
RESULT_SCHEMA = "axeyum-lean-execution-store-result-v1"
SUMMARY_SCHEMA = "axeyum-lean-execution-store-summary-v1"
PREREGISTRATION_COMMIT = "8bad614645137164eafec6ab6cf068e5035695b5"
HISTORICAL_IMPLEMENTATION_REVISION = "afe7db6e04c78fcbce04c6f502268ce2d9934121"
CONTROL_ID = "interrupted-resumed"
CREDIT_CLASS = "synthetic-no-credit"
STORAGE_CLASS_IDS = (
    "linux-local-worktree-hardlink-fsync-v1",
    "linux-tmpfs-hardlink-fsync-v1",
)
TARGET_ROLES = ("dependency", "completion")
TARGET_PATHS = {
    "dependency": "cases/case-a.json",
    "completion": "completion/completion.json",
}
PHASES = (
    "before_temp_open",
    "after_temp_fsync",
    "after_final_link",
    "after_commit",
)
EXPECTED_RESUME_OUTCOME = {
    "before_temp_open": "installed",
    "after_temp_fsync": "installed",
    "after_final_link": "existing-valid",
    "after_commit": "existing-valid",
}
EXPECTED_ORPHANS = {
    "before_temp_open": 0,
    "after_temp_fsync": 1,
    "after_final_link": 1,
    "after_commit": 0,
}
SAFE_ID = re.compile(r"[a-z0-9][a-z0-9.-]{0,127}\Z")
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
MOUNT_FIELDS = {
    "mount_point",
    "mount_root",
    "mount_source",
    "fs_type",
    "mount_options",
    "super_options",
    "mount_id",
    "parent_mount_id",
    "mount_major_minor",
}
STORAGE_DESCRIPTOR_FIELDS = {
    "id",
    "class_root",
    "mount",
    "stat_device",
    "stat_fsid",
    "statfs_magic",
    "block_size",
    "fragment_size",
    "name_max",
    "kernel",
    "mechanism",
    "process_interruption_proven",
    "power_loss_proven",
    "host_loss_proven",
    "network_storage_proven",
    "identity_sha256",
}
PROCESS_EVIDENCE_FIELDS = {
    "command",
    "command_sha256",
    "environment",
    "environment_sha256",
    "executable_sha256",
    "worker_sha256",
    "primitive_sha256",
    "pid",
    "process_group_id",
    "return_code",
    "signal",
    "marker_sha256",
    "stdout",
    "stderr",
}
NETWORK_FILESYSTEMS = {
    "9p",
    "afs",
    "ceph",
    "cifs",
    "fuse.sshfs",
    "gfs2",
    "lustre",
    "nfs",
    "nfs4",
    "smb3",
}
HISTORICAL_RESULT_SOURCE_INPUTS = (
    {
        "path": "docs/plan/lean-execution-store-tl0.7.3-plan-2026-07-22.md",
        "sha256": "77b9af8ad012d907c2aa8297008066117d476f0e8018a33278a5104892044263",
    },
    {
        "path": "scripts/lean_execution_store.py",
        "sha256": "06d388a49d927a2f1b65a4632cd6297b140a579cf80edd5177fc6849b62ec679",
    },
    {
        "path": "scripts/tests/test_lean_execution_store.py",
        "sha256": "1ef995ace9fccd59af05640c5b256782b9183e9c9665101df99127a24b65d72f",
    },
    {
        "path": "scripts/smtcomp_repro/resume_fs.py",
        "sha256": "1968e7b6424c2dd9273bff5041e96fc21b83ec01b2205dcc840d5dc942be1aec",
    },
    {
        "path": "scripts/smtcomp_repro/resume_fs_fixture_worker.py",
        "sha256": "a8ba281cc20e883f7b5e37d5010de50abf1dd60d7017d740188e53e2208e8810",
    },
    {
        "path": "scripts/gen-lean-execution-evidence.py",
        "sha256": "025f935111b83e1a3bbc78af50a4ad5671baa370bda02fe94756481e54f55418",
    },
    {
        "path": "docs/plan/lean-execution-evidence-v1.json",
        "sha256": "83fbfeaf6baa4c1bd747ce80bba87a15aaf159bb164a7647cc8e3155282fa05a",
    },
    {
        "path": "docs/plan/lean-execution-process-v1.json",
        "sha256": "0fc2d552f8594e2285eef2f0307a9b4d5313024166f0256486b731366947c0bf",
    },
)


class StoreEvidenceError(ValueError):
    """The Lean checkpoint store or retained matrix failed closed."""


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def digest(value: Any) -> str:
    return sha256_bytes(canonical_bytes(value))


def domain_digest(domain: str, value: Any) -> str:
    return sha256_bytes(domain.encode("ascii") + b"\0" + canonical_bytes(value))


def _root_for_repository_relative_path(path: str, relative: Path) -> Path | None:
    """Recover a checkout root from an absolute path and repository suffix."""
    candidate = Path(path)
    if not candidate.is_absolute() or relative.is_absolute() or ".." in relative.parts:
        return None
    for part in reversed(relative.parts):
        if candidate.name != part:
            return None
        candidate = candidate.parent
    return candidate


def object_digest(value: dict[str, Any], field: str) -> str:
    return digest({key: item for key, item in value.items() if key != field})


def _write_all(descriptor: int, data: bytes) -> None:
    offset = 0
    while offset < len(data):
        written = os.write(descriptor, data[offset:])
        if written <= 0:
            raise OSError("short checkpoint-evidence write")
        offset += written


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def write_new(path: Path, data: bytes, *, mode: int = 0o444) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(
        path,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0),
        0o600,
    )
    try:
        _write_all(descriptor, data)
        os.fchmod(descriptor, mode)
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    _fsync_directory(path.parent)


def load_canonical(path: Path) -> Any:
    try:
        raw = path.read_bytes()
        value = json.loads(raw)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise StoreEvidenceError(f"malformed canonical JSON: {path}") from exc
    if raw != canonical_bytes(value):
        raise StoreEvidenceError(f"noncanonical JSON: {path}")
    return value


def _decode_mount_field(value: str) -> str:
    for escaped, decoded in (("\\040", " "), ("\\011", "\t"), ("\\012", "\n"), ("\\134", "\\")):
        value = value.replace(escaped, decoded)
    return value


def mount_identity(path: Path) -> dict[str, Any]:
    path = path.resolve()
    try:
        lines = Path("/proc/self/mountinfo").read_text(encoding="utf-8").splitlines()
    except OSError as exc:
        raise StoreEvidenceError("Linux mountinfo is unavailable") from exc
    candidates = []
    for line in lines:
        parts = line.split()
        try:
            separator = parts.index("-")
        except ValueError:
            continue
        if separator < 6 or len(parts) < separator + 4:
            continue
        mount_point = Path(_decode_mount_field(parts[4]))
        try:
            path.relative_to(mount_point)
        except ValueError:
            continue
        candidates.append(
            (
                len(mount_point.parts),
                {
                    "mount_point": str(mount_point),
                    "mount_root": _decode_mount_field(parts[3]),
                    "mount_source": _decode_mount_field(parts[separator + 2]),
                    "fs_type": parts[separator + 1],
                    "mount_options": sorted(set(parts[5].split(","))),
                    "super_options": sorted(set(parts[separator + 3].split(","))),
                    "mount_id": int(parts[0]),
                    "parent_mount_id": int(parts[1]),
                    "mount_major_minor": parts[2],
                },
            )
        )
    if not candidates:
        raise StoreEvidenceError(f"no mountinfo entry contains {path}")
    return max(candidates, key=lambda item: item[0])[1]


def statfs_magic(path: Path) -> str:
    executable = shutil.which("stat")
    if executable is None:
        raise StoreEvidenceError("statfs identity probe is unavailable")
    try:
        completed = subprocess.run(
            [os.path.realpath(executable), "--file-system", "--format=%t", "--", str(path)],
            cwd=ROOT,
            env={"LANG": "C", "PATH": os.path.dirname(os.path.realpath(executable))},
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=5,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise StoreEvidenceError("statfs identity probe failed") from exc
    value = completed.stdout.decode("ascii", errors="strict").strip()
    if completed.returncode != 0 or not re.fullmatch(r"[0-9a-f]+", value):
        raise StoreEvidenceError("statfs identity probe returned no Linux magic")
    return value


def validate_storage_descriptor(descriptor: Any) -> list[str]:
    failures: list[str] = []
    if not isinstance(descriptor, dict) or set(descriptor) != STORAGE_DESCRIPTOR_FIELDS:
        return ["storage descriptor fields must be exact"]
    class_id = descriptor.get("id")
    mount = descriptor.get("mount")
    if class_id not in STORAGE_CLASS_IDS:
        failures.append("storage descriptor class drift")
    if not isinstance(mount, dict) or set(mount) != MOUNT_FIELDS:
        failures.append("storage mount identity fields must be exact")
        mount = {}
    for field in ("mount_point", "mount_root", "mount_source", "fs_type", "mount_major_minor"):
        if not isinstance(mount.get(field), str) or not mount.get(field):
            failures.append(f"storage mount {field} identity is required")
    for field in ("mount_id", "parent_mount_id"):
        value = mount.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            failures.append(f"storage mount {field} must be a nonnegative integer")
    mount_options = mount.get("mount_options")
    super_options = mount.get("super_options")
    if not isinstance(mount_options, list) or not all(
        isinstance(item, str) and item for item in mount_options
    ):
        failures.append("storage mount options must be non-empty strings")
        mount_options = []
    elif mount_options != sorted(set(mount_options)):
        failures.append("storage mount options must be unique and sorted")
    if not isinstance(super_options, list) or not all(
        isinstance(item, str) and item for item in super_options
    ):
        failures.append("storage super options must be non-empty strings")
    elif super_options != sorted(set(super_options)):
        failures.append("storage super options must be unique and sorted")
    if descriptor.get("identity_sha256") != object_digest(descriptor, "identity_sha256"):
        failures.append("storage descriptor identity drift")
    if descriptor.get("mechanism") != "o-excl-temp-file-fsync-hardlink-no-replace-directory-fsync-v1":
        failures.append("storage mechanism drift")
    if any(
        descriptor.get(field) is not False
        for field in (
            "process_interruption_proven",
            "power_loss_proven",
            "host_loss_proven",
            "network_storage_proven",
        )
    ):
        failures.append("storage descriptor cannot preclaim interruption or durability")
    fs_type = mount.get("fs_type")
    if fs_type in NETWORK_FILESYSTEMS:
        failures.append("network filesystem cannot enter TL0.7.3")
    if "ro" in mount_options or "rw" not in mount_options:
        failures.append("storage class must be an observed writable mount")
    magic = descriptor.get("statfs_magic")
    if not isinstance(magic, str) or not re.fullmatch(r"[0-9a-f]+", magic):
        failures.append("storage statfs magic is invalid")
    if fs_type in {"ext2", "ext3", "ext4"} and magic != "ef53":
        failures.append("ext-family mount/statfs identity mismatch")
    if class_id == STORAGE_CLASS_IDS[1]:
        if fs_type != "tmpfs" or magic != "1021994":
            failures.append("tmpfs storage class identity mismatch")
        if Path(str(descriptor.get("class_root"))).resolve() != Path("/dev/shm").resolve():
            failures.append("tmpfs storage class root drift")
    class_root = Path(str(descriptor.get("class_root")))
    mount_point = Path(str(mount.get("mount_point")))
    if not class_root.is_absolute() or not mount_point.is_absolute():
        failures.append("storage class and mount roots must be absolute")
    else:
        try:
            class_root.resolve().relative_to(mount_point.resolve())
        except ValueError:
            failures.append("storage class root is outside its observed mount")
    for field in ("stat_device", "stat_fsid", "block_size", "fragment_size", "name_max"):
        value = descriptor.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            failures.append(f"storage descriptor {field} must be a nonnegative integer")
    if not isinstance(descriptor.get("kernel"), str) or not descriptor["kernel"]:
        failures.append("storage kernel identity is required")
    return failures


def capture_storage_class(class_id: str, parent: Path) -> dict[str, Any]:
    if class_id not in STORAGE_CLASS_IDS:
        raise StoreEvidenceError(f"unknown storage class: {class_id}")
    parent = parent.resolve()
    if not parent.is_dir():
        raise StoreEvidenceError(f"storage class parent is not a directory: {parent}")
    mount = mount_identity(parent)
    fs_type = mount["fs_type"]
    if fs_type in NETWORK_FILESYSTEMS:
        raise StoreEvidenceError("network filesystem cannot enter TL0.7.3")
    if class_id == "linux-tmpfs-hardlink-fsync-v1" and fs_type != "tmpfs":
        raise StoreEvidenceError("tmpfs storage class requires observed tmpfs")
    if class_id == "linux-local-worktree-hardlink-fsync-v1" and parent != ROOT:
        raise StoreEvidenceError("worktree storage class must use repository root")
    stat_result = parent.stat()
    statvfs = os.statvfs(parent)
    descriptor: dict[str, Any] = {
        "id": class_id,
        "class_root": str(parent),
        "mount": mount,
        "stat_device": stat_result.st_dev,
        "stat_fsid": statvfs.f_fsid,
        "statfs_magic": statfs_magic(parent),
        "block_size": statvfs.f_bsize,
        "fragment_size": statvfs.f_frsize,
        "name_max": statvfs.f_namemax,
        "kernel": platform.release(),
        "mechanism": "o-excl-temp-file-fsync-hardlink-no-replace-directory-fsync-v1",
        "process_interruption_proven": False,
        "power_loss_proven": False,
        "host_loss_proven": False,
        "network_storage_proven": False,
        "identity_sha256": "",
    }
    descriptor["identity_sha256"] = object_digest(descriptor, "identity_sha256")
    failures = validate_storage_descriptor(descriptor)
    if failures:
        raise StoreEvidenceError("; ".join(failures))
    return descriptor


def preflight_storage_class(descriptor: dict[str, Any]) -> None:
    failures = validate_storage_descriptor(descriptor)
    if failures:
        raise StoreEvidenceError("; ".join(failures))
    parent = Path(descriptor["class_root"])
    with tempfile.TemporaryDirectory(prefix=".axeyum-lean-store-preflight-", dir=parent) as temporary:
        directory = Path(temporary)
        source = directory / "source"
        final = directory / "final"
        payload = b"axeyum-lean-store-preflight-v1\n"
        descriptor_fd = os.open(
            source,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0),
            0o600,
        )
        try:
            _write_all(descriptor_fd, payload)
            os.fsync(descriptor_fd)
            os.link(source, final)
            try:
                os.link(source, final)
            except FileExistsError:
                pass
            else:
                raise StoreEvidenceError("hard-link final unexpectedly replaced")
            os.fsync(descriptor_fd)
        finally:
            os.close(descriptor_fd)
        _fsync_directory(directory)
        if final.read_bytes() != payload or source.stat().st_ino != final.stat().st_ino:
            raise StoreEvidenceError("hard-link/fsync preflight readback failed")


def fixture_bundle() -> dict[str, Any]:
    bundle = EVIDENCE_CONTRACT.synthetic_bundle(CONTROL_ID)
    failures = EVIDENCE_CONTRACT.validate_bundle(bundle)
    if failures:
        raise StoreEvidenceError("base TL0.7.1 fixture invalid: " + "; ".join(failures))
    if bundle["credits"] != EVIDENCE_CONTRACT.zero_credits():
        raise StoreEvidenceError("store fixture must retain all-zero credits")
    return bundle


def fixture_dependencies() -> list[tuple[str, dict[str, Any]]]:
    bundle = fixture_bundle()
    rows: list[tuple[str, dict[str, Any]]] = [("run/run.json", bundle["run"])]
    rows.extend((f"attempts/{item['id']}.json", item) for item in bundle["attempts"])
    rows.extend((f"cases/{item['id']}.json", item) for item in bundle["cases"])
    rows.extend((f"artifacts/{item['id']}.json", item) for item in bundle["artifacts"])
    return rows


def fixture_completion() -> dict[str, Any]:
    completion = fixture_bundle()["completion"]
    if not isinstance(completion, dict):
        raise StoreEvidenceError("interrupted/resumed fixture lacks completion")
    return completion


def build_store_manifest(storage_class: dict[str, Any]) -> dict[str, Any]:
    dependencies = [
        {"path": path, "sha256": sha256_bytes(canonical_bytes(value))}
        for path, value in fixture_dependencies()
    ]
    completion = fixture_completion()
    manifest: dict[str, Any] = {
        "schema": STORE_SCHEMA,
        "control_id": CONTROL_ID,
        "credit_class": CREDIT_CLASS,
        "storage_class": storage_class,
        "dependency_records": dependencies,
        "completion_record": {
            "path": TARGET_PATHS["completion"],
            "sha256": sha256_bytes(canonical_bytes(completion)),
        },
        "completion_installed_last": True,
        "real_outcomes": 0,
        "parity_credit": 0,
        "record_sha256": "",
    }
    manifest["record_sha256"] = domain_digest(
        STORE_SCHEMA,
        {key: value for key, value in manifest.items() if key != "record_sha256"},
    )
    return manifest


def validate_store_manifest(manifest: Any) -> list[str]:
    failures: list[str] = []
    fields = {
        "schema",
        "control_id",
        "credit_class",
        "storage_class",
        "dependency_records",
        "completion_record",
        "completion_installed_last",
        "real_outcomes",
        "parity_credit",
        "record_sha256",
    }
    if not isinstance(manifest, dict) or set(manifest) != fields:
        return ["store manifest fields must be exact"]
    claimed = manifest.get("record_sha256")
    expected_hash = domain_digest(
        STORE_SCHEMA,
        {key: value for key, value in manifest.items() if key != "record_sha256"},
    )
    if manifest.get("schema") != STORE_SCHEMA or claimed != expected_hash:
        failures.append("store manifest identity drift")
    storage = manifest.get("storage_class")
    storage_failures = validate_storage_descriptor(storage)
    if storage_failures:
        failures.extend(f"store {failure}" for failure in storage_failures)
    expected = build_store_manifest(storage) if isinstance(storage, dict) else None
    if expected is not None and manifest != expected:
        failures.append("store manifest differs from exact fixture/storage contract")
    if manifest.get("real_outcomes") != 0 or manifest.get("parity_credit") != 0:
        failures.append("store manifest cannot claim real or parity credit")
    return failures


def _install_relative(root: Path, relative: str, value: dict[str, Any]) -> str:
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts or len(path.parts) != 2:
        raise StoreEvidenceError(f"unsafe store record path: {relative}")
    if root.is_symlink() or not root.is_dir():
        raise StoreEvidenceError("store root must be a real directory")
    directory = root / path.parent
    if directory.is_symlink() or (directory.exists() and not directory.is_dir()):
        raise StoreEvidenceError(
            f"store namespace is not a real directory: {path.parent.as_posix()}"
        )
    quarantine = root / "quarantine"
    if quarantine.is_symlink() or (quarantine.exists() and not quarantine.is_dir()):
        raise StoreEvidenceError("store quarantine must be a real directory")
    return atomic_install_json(
        directory,
        path.name,
        value,
        quarantine_root=quarantine,
    )


def initialize_store(root: Path, storage_class: dict[str, Any]) -> str:
    failures = validate_storage_descriptor(storage_class)
    if failures:
        raise StoreEvidenceError("; ".join(failures))
    if root.is_symlink() or root.exists():
        raise StoreEvidenceError(f"store root must be new: {root}")
    root.mkdir(parents=True, mode=0o755)
    return atomic_install_json(
        root,
        "store.json",
        build_store_manifest(storage_class),
        quarantine_root=root / "quarantine",
    )


def install_dependencies(root: Path, *, omit: str | None = None) -> list[tuple[str, str]]:
    outcomes = []
    for relative, value in fixture_dependencies():
        if relative == omit:
            continue
        outcomes.append((relative, _install_relative(root, relative, value)))
    return outcomes


def _accepted_record_paths(manifest: dict[str, Any], *, include_completion: bool) -> list[str]:
    paths = ["store.json"] + [item["path"] for item in manifest["dependency_records"]]
    if include_completion:
        paths.append(manifest["completion_record"]["path"])
    return paths


def _strict_namespace(root: Path, *, require_completion: bool) -> tuple[dict[str, Any], dict[str, Any]]:
    if not root.is_dir() or root.is_symlink():
        raise StoreEvidenceError("store root must be a real directory")
    allowed_top = {"store.json", "run", "attempts", "cases", "artifacts", "completion", "quarantine"}
    top_entries = list(root.iterdir())
    extras = sorted(path.name for path in top_entries if path.name not in allowed_top)
    if extras:
        raise StoreEvidenceError(f"unexpected store entry: {extras[0]}")
    for path in top_entries:
        if path.name == "store.json":
            continue
        if path.is_symlink() or not path.is_dir():
            raise StoreEvidenceError(f"store namespace is not a real directory: {path.name}")
    manifest_path = root / "store.json"
    if manifest_path.is_symlink() or not manifest_path.is_file():
        raise StoreEvidenceError("missing real store manifest")
    manifest = load_canonical(manifest_path)
    failures = validate_store_manifest(manifest)
    if failures:
        raise StoreEvidenceError("; ".join(failures))
    expected_hashes = {
        item["path"]: item["sha256"] for item in manifest["dependency_records"]
    }
    expected_hashes[manifest["completion_record"]["path"]] = manifest["completion_record"]["sha256"]
    expected_by_directory: dict[str, set[str]] = {name: set() for name in ("run", "attempts", "cases", "artifacts", "completion")}
    for relative in expected_hashes:
        directory, filename = relative.split("/", 1)
        expected_by_directory[directory].add(filename)
    records: dict[str, Any] = {}
    for directory_name, expected_names in expected_by_directory.items():
        directory = root / directory_name
        if not directory.exists():
            if directory_name == "completion" and not require_completion:
                continue
            raise StoreEvidenceError(f"missing store directory: {directory_name}")
        if directory.is_symlink() or not directory.is_dir():
            raise StoreEvidenceError(f"store namespace is not a real directory: {directory_name}")
        entries = sorted(directory.iterdir(), key=lambda path: path.name)
        for path in entries:
            if path.is_symlink() or not path.is_file() or path.suffix != ".json":
                raise StoreEvidenceError(f"invalid store record: {path.relative_to(root)}")
        present = {path.name for path in entries}
        allowed = expected_names
        if directory_name == "completion" and not require_completion:
            allowed = set()
        unexpected = sorted(present - allowed)
        if unexpected:
            raise StoreEvidenceError(f"unexpected store record: {directory_name}/{unexpected[0]}")
        if directory_name != "completion" or require_completion:
            missing = sorted(allowed - present)
            if missing:
                raise StoreEvidenceError(f"missing store record: {directory_name}/{missing[0]}")
        for path in entries:
            relative = path.relative_to(root).as_posix()
            if path.stat().st_mode & 0o777 != 0o444:
                raise StoreEvidenceError(f"accepted record is not read-only: {relative}")
            raw = path.read_bytes()
            if sha256_bytes(raw) != expected_hashes[relative]:
                raise StoreEvidenceError(f"record content identity drift: {relative}")
            value = load_canonical(path)
            stem = path.stem
            if directory_name in {"attempts", "cases", "artifacts"} and value.get("id") != stem:
                raise StoreEvidenceError(f"record filename/id mismatch: {relative}")
            records[relative] = value
    return manifest, records


def _bundle_from_records(records: dict[str, Any], *, require_completion: bool) -> dict[str, Any]:
    bundle = fixture_bundle()
    bundle["run"] = records["run/run.json"]
    bundle["attempts"] = [
        records[f"attempts/{item['id']}.json"] for item in bundle["attempts"]
    ]
    bundle["cases"] = [records[f"cases/{item['id']}.json"] for item in bundle["cases"]]
    bundle["artifacts"] = [
        records[f"artifacts/{item['id']}.json"] for item in bundle["artifacts"]
    ]
    bundle["completion"] = records.get("completion/completion.json") if require_completion else None
    bundle["credits"] = EVIDENCE_CONTRACT.zero_credits()
    return bundle


def validate_dependencies(root: Path) -> None:
    manifest, records = _strict_namespace(root, require_completion=False)
    completion_path = root / manifest["completion_record"]["path"]
    if completion_path.exists():
        raise StoreEvidenceError("completion already exists during dependency validation")
    bundle = _bundle_from_records(records, require_completion=False)
    expected = fixture_bundle()
    for field in ("run", "attempts", "cases", "artifacts", "credits"):
        if bundle[field] != expected[field]:
            raise StoreEvidenceError(f"dependency bundle drift: {field}")
    candidate = copy.deepcopy(bundle)
    candidate["completion"] = fixture_completion()
    failures = EVIDENCE_CONTRACT.validate_bundle(candidate)
    if failures:
        raise StoreEvidenceError("completion dependency closure invalid: " + "; ".join(failures))


def install_completion(root: Path) -> str:
    completion_path = root / TARGET_PATHS["completion"]
    if not completion_path.exists():
        validate_dependencies(root)
    else:
        # Resume may observe a completion hard-linked before the killed worker's
        # directory fsync. Dependencies still have to validate exactly.
        manifest, records = _strict_namespace(root, require_completion=True)
        records_without_completion = dict(records)
        records_without_completion.pop(manifest["completion_record"]["path"])
        bundle = _bundle_from_records(records_without_completion, require_completion=False)
        candidate = copy.deepcopy(bundle)
        candidate["completion"] = fixture_completion()
        failures = EVIDENCE_CONTRACT.validate_bundle(candidate)
        if failures:
            raise StoreEvidenceError("resumed completion dependency closure invalid: " + "; ".join(failures))
    return _install_relative(root, TARGET_PATHS["completion"], fixture_completion())


def validate_complete_store(root: Path) -> bytes:
    manifest, records = _strict_namespace(root, require_completion=True)
    bundle = _bundle_from_records(records, require_completion=True)
    failures = EVIDENCE_CONTRACT.validate_bundle(bundle)
    if failures:
        raise StoreEvidenceError("completed store invalid: " + "; ".join(failures))
    if bundle["credits"] != EVIDENCE_CONTRACT.zero_credits():
        raise StoreEvidenceError("completed store cannot claim credit")
    projection = {
        "schema": "axeyum-lean-execution-store-projection-v1",
        "store_record_sha256": manifest["record_sha256"],
        "records": [
            {
                "path": relative,
                "sha256": sha256_file(root / relative),
            }
            for relative in sorted(_accepted_record_paths(manifest, include_completion=True))
        ],
        "completion_sha256": bundle["completion"]["sha256"],
        "credits": bundle["credits"],
    }
    return canonical_bytes(projection)


def accepted_inventory(root: Path) -> list[dict[str, Any]]:
    rows = []
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        relative = path.relative_to(root)
        if relative.parts and relative.parts[0] == "quarantine":
            continue
        if path.name.startswith(".") and ".tmp-" in path.name:
            continue
        rows.append({"path": relative.as_posix(), "bytes": path.stat().st_size, "sha256": sha256_file(path)})
    return rows


def recover_store_orphans(root: Path) -> list[Path]:
    if root.is_symlink() or not root.is_dir():
        raise StoreEvidenceError("store root must be a real directory")
    quarantine = root / "quarantine"
    if quarantine.is_symlink() or (quarantine.exists() and not quarantine.is_dir()):
        raise StoreEvidenceError("store quarantine must be a real directory")
    recovered = []
    for directory_name in ("run", "attempts", "cases", "artifacts", "completion"):
        directory = root / directory_name
        if directory.is_symlink() or (directory.exists() and not directory.is_dir()):
            raise StoreEvidenceError(
                f"store namespace is not a real directory: {directory_name}"
            )
        recovered.extend(
            recover_orphan_temporaries(
                directory, quarantine_root=quarantine
            )
        )
    return recovered


def _wait_for_marker(marker: Path, process: subprocess.Popen[bytes]) -> None:
    deadline = time.monotonic() + 5.0
    while time.monotonic() < deadline:
        if marker.is_file():
            return
        if process.poll() is not None:
            raise StoreEvidenceError(f"kill worker exited before marker: {process.returncode}")
        time.sleep(0.01)
    raise StoreEvidenceError("kill worker did not reach persistence marker")


def _kill_worker(
    *,
    store_root: Path,
    target_path: str,
    target_value: dict[str, Any],
    phase: str,
    work_root: Path,
    evidence_directory: Path,
) -> dict[str, Any]:
    payload = work_root / "payload.json"
    marker = work_root / "phase.marker"
    write_new(payload, canonical_bytes(target_value))
    evidence_directory.mkdir(parents=True, exist_ok=False)
    stdout_path = evidence_directory / "stdout.bin"
    stderr_path = evidence_directory / "stderr.bin"
    stdout = stdout_path.open("xb", buffering=0)
    stderr = stderr_path.open("xb", buffering=0)
    command = [
        os.path.realpath(sys.executable),
        str(WORKER.resolve()),
        "--directory",
        str(store_root / Path(target_path).parent),
        "--filename",
        Path(target_path).name,
        "--payload",
        str(payload),
        "--stop-phase",
        phase,
        "--marker",
        str(marker),
    ]
    environment = {
        "LANG": "C.UTF-8",
        "PYTHONHASHSEED": "0",
        "PYTHONPATH": str(SMTCOMP),
    }
    process = subprocess.Popen(
        command,
        cwd=SMTCOMP,
        env=environment,
        stdin=subprocess.DEVNULL,
        stdout=stdout,
        stderr=stderr,
        shell=False,
        close_fds=True,
        start_new_session=True,
    )
    try:
        _wait_for_marker(marker, process)
        os.killpg(process.pid, signal.SIGKILL)
        process.wait(timeout=5)
    finally:
        if process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait(timeout=5)
        stdout.close()
        stderr.close()
    marker_bytes = marker.read_bytes()
    expected_marker = (phase + "\n").encode()
    if marker_bytes != expected_marker:
        raise StoreEvidenceError("persistence marker bytes drifted")
    if process.returncode != -signal.SIGKILL:
        raise StoreEvidenceError("kill worker did not terminate by SIGKILL")
    write_new(evidence_directory / "marker.bin", marker_bytes)
    return {
        "command": command,
        "command_sha256": digest(command),
        "environment": environment,
        "environment_sha256": digest(environment),
        "executable_sha256": sha256_file(Path(command[0])),
        "worker_sha256": sha256_file(WORKER),
        "primitive_sha256": sha256_file(PRIMITIVE),
        "pid": process.pid,
        "process_group_id": process.pid,
        "return_code": process.returncode,
        "signal": signal.SIGKILL,
        "marker_sha256": sha256_bytes(marker_bytes),
        "stdout": {"sha256": sha256_file(stdout_path), "bytes": stdout_path.stat().st_size},
        "stderr": {"sha256": sha256_file(stderr_path), "bytes": stderr_path.stat().st_size},
    }


def _cell_id(storage_class_id: str, target_role: str, phase: str) -> str:
    storage = "worktree" if storage_class_id == STORAGE_CLASS_IDS[0] else "tmpfs"
    return f"{storage}--{target_role}--{phase.replace('_', '-')}"


def run_kill_cell(
    *,
    storage_class: dict[str, Any],
    target_role: str,
    phase: str,
    baseline_projection_sha256: str,
    evidence_directory: Path,
) -> dict[str, Any]:
    if target_role not in TARGET_ROLES or phase not in PHASES:
        raise StoreEvidenceError("unknown kill cell")
    parent = Path(storage_class["class_root"])
    with tempfile.TemporaryDirectory(prefix=".axeyum-lean-store-cell-", dir=parent) as temporary:
        work_root = Path(temporary)
        store_root = work_root / "store"
        initialize_store(store_root, storage_class)
        target_path = TARGET_PATHS[target_role]
        if target_role == "dependency":
            install_dependencies(store_root, omit=target_path)
            target_value = dict(fixture_dependencies())[target_path]
        else:
            install_dependencies(store_root)
            validate_dependencies(store_root)
            target_value = fixture_completion()
        pre_inventory = accepted_inventory(store_root)
        process_evidence = _kill_worker(
            store_root=store_root,
            target_path=target_path,
            target_value=target_value,
            phase=phase,
            work_root=work_root,
            evidence_directory=evidence_directory,
        )
        post_kill_inventory = accepted_inventory(store_root)
        recovered = recover_store_orphans(store_root)
        orphan_rows = sorted(
            ({"bytes": path.stat().st_size, "sha256": sha256_file(path)} for path in recovered),
            key=lambda row: (row["sha256"], row["bytes"]),
        )
        if len(orphan_rows) != EXPECTED_ORPHANS[phase]:
            raise StoreEvidenceError("orphan recovery count differs from persistence phase")
        if target_role == "dependency":
            resume_outcome = _install_relative(store_root, target_path, target_value)
            install_completion(store_root)
        else:
            resume_outcome = install_completion(store_root)
        if resume_outcome != EXPECTED_RESUME_OUTCOME[phase]:
            raise StoreEvidenceError("resume outcome differs from persistence phase")
        projection = validate_complete_store(store_root)
        projection_sha256 = sha256_bytes(projection)
        if projection_sha256 != baseline_projection_sha256:
            raise StoreEvidenceError("interrupted/resumed projection differs from uninterrupted reference")
        final_inventory = accepted_inventory(store_root)
        completion = load_canonical(store_root / TARGET_PATHS["completion"])
        cell: dict[str, Any] = {
            "schema": CELL_SCHEMA,
            "control_id": _cell_id(storage_class["id"], target_role, phase),
            "fixture_id": CONTROL_ID,
            "credit_class": CREDIT_CLASS,
            "storage_class_id": storage_class["id"],
            "storage_identity_sha256": storage_class["identity_sha256"],
            "target_role": target_role,
            "target_path": target_path,
            "phase": phase,
            "process": process_evidence,
            "pre_inventory_sha256": digest(pre_inventory),
            "post_kill_inventory_sha256": digest(post_kill_inventory),
            "orphan_count": len(orphan_rows),
            "orphan_records": orphan_rows,
            "resume_outcome": resume_outcome,
            "final_inventory_sha256": digest(final_inventory),
            "canonical_projection_sha256": projection_sha256,
            "baseline_projection_sha256": baseline_projection_sha256,
            "completion_sha256": completion["sha256"],
            "real_outcomes": 0,
            "parity_credit": 0,
            "record_sha256": "",
        }
        cell["record_sha256"] = domain_digest(
            CELL_SCHEMA,
            {key: value for key, value in cell.items() if key != "record_sha256"},
        )
        write_new(evidence_directory / "cell.json", canonical_bytes(cell))
        return cell


def uninterrupted_projection(storage_class: dict[str, Any]) -> bytes:
    parent = Path(storage_class["class_root"])
    with tempfile.TemporaryDirectory(prefix=".axeyum-lean-store-baseline-", dir=parent) as temporary:
        root = Path(temporary) / "store"
        initialize_store(root, storage_class)
        install_dependencies(root)
        install_completion(root)
        return validate_complete_store(root)


def build_storage_classes_document(classes: list[dict[str, Any]], baselines: dict[str, str]) -> dict[str, Any]:
    document: dict[str, Any] = {
        "schema": STORAGE_CLASSES_SCHEMA,
        "storage_classes": classes,
        "baseline_projection_sha256": baselines,
        "process_interruption_only": True,
        "power_loss_proven": False,
        "record_sha256": "",
    }
    document["record_sha256"] = domain_digest(
        STORAGE_CLASSES_SCHEMA,
        {key: value for key, value in document.items() if key != "record_sha256"},
    )
    return document


def run_matrix(*, output_root: Path, worktree_parent: Path = ROOT, tmpfs_parent: Path = Path("/dev/shm")) -> None:
    if output_root.exists():
        raise StoreEvidenceError(f"matrix output root must be new: {output_root}")
    output_root.mkdir(parents=True)
    class_parents = {
        STORAGE_CLASS_IDS[0]: worktree_parent,
        STORAGE_CLASS_IDS[1]: tmpfs_parent,
    }
    classes = []
    baselines = {}
    for class_id in STORAGE_CLASS_IDS:
        descriptor = capture_storage_class(class_id, class_parents[class_id])
        preflight_storage_class(descriptor)
        classes.append(descriptor)
        baselines[class_id] = sha256_bytes(uninterrupted_projection(descriptor))
    storage_document = build_storage_classes_document(classes, baselines)
    write_new(output_root / "storage-classes.json", canonical_bytes(storage_document))
    for descriptor in classes:
        for target_role in TARGET_ROLES:
            for phase in PHASES:
                control_id = _cell_id(descriptor["id"], target_role, phase)
                cell = run_kill_cell(
                    storage_class=descriptor,
                    target_role=target_role,
                    phase=phase,
                    baseline_projection_sha256=baselines[descriptor["id"]],
                    evidence_directory=output_root / control_id,
                )
                print(
                    "LEAN_STORE_CELL|"
                    f"id={cell['control_id']}|signal=9|resume={cell['resume_outcome']}|"
                    "projection=equal|credit=zero"
                )


def validate_process_evidence(
    process: Any,
    *,
    target_path: str,
    phase: str,
    evidence_directory: Path,
    expected_worker_sha256: str | None = None,
    expected_primitive_sha256: str | None = None,
) -> list[str]:
    failures: list[str] = []
    if not isinstance(process, dict) or set(process) != PROCESS_EVIDENCE_FIELDS:
        return ["kill cell process evidence fields must be exact"]
    if process.get("return_code") != -signal.SIGKILL or process.get("signal") != signal.SIGKILL:
        failures.append("kill cell is not a reaped SIGKILL")
    pid = process.get("pid")
    if (
        not isinstance(pid, int)
        or isinstance(pid, bool)
        or pid <= 0
        or process.get("process_group_id") != pid
    ):
        failures.append("kill cell process/group identity drift")
    command = process.get("command")
    expected_prefixes = (
        os.path.realpath(sys.executable),
        None,
        "--directory",
        None,
        "--filename",
        Path(target_path).name,
        "--payload",
        None,
        "--stop-phase",
        phase,
        "--marker",
        None,
    )
    recorded_root = None
    if not isinstance(command, list) or len(command) != len(expected_prefixes):
        failures.append("kill cell command fields drift")
    else:
        for actual, expected in zip(command, expected_prefixes, strict=True):
            if expected is not None and actual != expected:
                failures.append("kill cell command semantics drift")
                break
        if isinstance(command[1], str):
            recorded_root = _root_for_repository_relative_path(
                command[1], WORKER.relative_to(ROOT)
            )
        if recorded_root is None:
            failures.append("kill cell command semantics drift")
        if all(isinstance(command[index], str) for index in (3, 7, 11)):
            target_directory = Path(command[3])
            payload = Path(command[7])
            marker = Path(command[11])
            if (
                target_directory.name != Path(target_path).parent.name
                or target_directory.parent.name != "store"
                or target_directory.parent.parent != payload.parent
                or payload.parent != marker.parent
                or payload.name != "payload.json"
                or marker.name != "phase.marker"
            ):
                failures.append("kill cell ephemeral command paths drift")
        else:
            failures.append("kill cell command path types drift")
    expected_environment = {
        "LANG": "C.UTF-8",
        "PYTHONHASHSEED": "0",
        "PYTHONPATH": str(
            recorded_root / SMTCOMP.relative_to(ROOT)
            if recorded_root is not None
            else SMTCOMP
        ),
    }
    if process.get("environment") != expected_environment:
        failures.append("kill cell environment drift")
    if process.get("environment_sha256") != digest(process.get("environment")):
        failures.append("kill cell environment identity drift")
    if process.get("command_sha256") != digest(command):
        failures.append("kill cell command identity drift")
    executable = Path(os.path.realpath(sys.executable))
    if process.get("executable_sha256") != sha256_file(executable):
        failures.append("kill cell executable identity drift")
    if expected_worker_sha256 is None:
        expected_worker_sha256 = sha256_file(WORKER)
    if expected_primitive_sha256 is None:
        expected_primitive_sha256 = sha256_file(PRIMITIVE)
    if (
        process.get("worker_sha256") != expected_worker_sha256
        or process.get("primitive_sha256") != expected_primitive_sha256
    ):
        failures.append("kill cell source identity drift")
    for kind in ("stdout", "stderr"):
        path = evidence_directory / f"{kind}.bin"
        expected = process.get(kind)
        if (
            not isinstance(expected, dict)
            or set(expected) != {"sha256", "bytes"}
            or HEX64.fullmatch(str(expected.get("sha256"))) is None
            or not isinstance(expected.get("bytes"), int)
            or isinstance(expected.get("bytes"), bool)
            or expected["bytes"] < 0
            or path.is_symlink()
            or not path.is_file()
            or expected
            != {
                "sha256": sha256_file(path),
                "bytes": path.stat().st_size,
            }
        ):
            failures.append(f"kill cell {kind} identity drift")
    marker = evidence_directory / "marker.bin"
    if (
        marker.is_symlink()
        or not marker.is_file()
        or marker.read_bytes() != (phase + "\n").encode()
        or process.get("marker_sha256") != sha256_file(marker)
    ):
        failures.append("kill cell marker identity drift")
    return failures


def validate_cell(
    cell: Any,
    *,
    storage_document: dict[str, Any],
    evidence_directory: Path,
    expected_worker_sha256: str | None = None,
    expected_primitive_sha256: str | None = None,
) -> list[str]:
    failures: list[str] = []
    fields = {
        "schema",
        "control_id",
        "fixture_id",
        "credit_class",
        "storage_class_id",
        "storage_identity_sha256",
        "target_role",
        "target_path",
        "phase",
        "process",
        "pre_inventory_sha256",
        "post_kill_inventory_sha256",
        "orphan_count",
        "orphan_records",
        "resume_outcome",
        "final_inventory_sha256",
        "canonical_projection_sha256",
        "baseline_projection_sha256",
        "completion_sha256",
        "real_outcomes",
        "parity_credit",
        "record_sha256",
    }
    if not isinstance(cell, dict) or set(cell) != fields:
        return ["kill cell fields must be exact"]
    expected_hash = domain_digest(
        CELL_SCHEMA,
        {key: value for key, value in cell.items() if key != "record_sha256"},
    )
    if cell.get("schema") != CELL_SCHEMA or cell.get("record_sha256") != expected_hash:
        failures.append("kill cell identity drift")
    class_map = {item["id"]: item for item in storage_document["storage_classes"]}
    descriptor = class_map.get(cell.get("storage_class_id"))
    if descriptor is None or cell.get("storage_identity_sha256") != descriptor["identity_sha256"]:
        failures.append("kill cell storage identity drift")
    target_role = cell.get("target_role")
    phase = cell.get("phase")
    if target_role not in TARGET_ROLES or phase not in PHASES:
        failures.append("kill cell target/phase drift")
    else:
        expected_id = _cell_id(cell["storage_class_id"], target_role, phase)
        if cell.get("control_id") != expected_id or cell.get("target_path") != TARGET_PATHS[target_role]:
            failures.append("kill cell control identity drift")
        if cell.get("resume_outcome") != EXPECTED_RESUME_OUTCOME[phase]:
            failures.append("kill cell resume outcome drift")
        orphan_records = cell.get("orphan_records")
        if not isinstance(orphan_records, list):
            failures.append("kill cell orphan records must be a list")
            orphan_records = []
        valid_orphans = all(
            isinstance(row, dict)
            and set(row) == {"sha256", "bytes"}
            and HEX64.fullmatch(str(row.get("sha256"))) is not None
            and isinstance(row.get("bytes"), int)
            and not isinstance(row.get("bytes"), bool)
            and row["bytes"] >= 0
            for row in orphan_records
        )
        if not valid_orphans:
            failures.append("kill cell orphan record identity drift")
        if cell.get("orphan_count") != EXPECTED_ORPHANS[phase] or len(orphan_records) != EXPECTED_ORPHANS[phase]:
            failures.append("kill cell orphan partition drift")
    if target_role in TARGET_ROLES and phase in PHASES:
        failures.extend(
            validate_process_evidence(
                cell.get("process"),
                target_path=TARGET_PATHS[target_role],
                phase=phase,
                evidence_directory=evidence_directory,
                expected_worker_sha256=expected_worker_sha256,
                expected_primitive_sha256=expected_primitive_sha256,
            )
        )
    else:
        failures.append("kill cell process evidence cannot be attributed")
    baseline = storage_document["baseline_projection_sha256"].get(cell.get("storage_class_id"))
    if cell.get("baseline_projection_sha256") != baseline or cell.get("canonical_projection_sha256") != baseline:
        failures.append("kill cell projection differs from uninterrupted baseline")
    for field in ("pre_inventory_sha256", "post_kill_inventory_sha256", "final_inventory_sha256"):
        if HEX64.fullmatch(str(cell.get(field))) is None:
            failures.append(f"kill cell {field} identity drift")
    if cell.get("completion_sha256") != fixture_completion()["sha256"]:
        failures.append("kill cell completion identity drift")
    if cell.get("fixture_id") != CONTROL_ID or cell.get("credit_class") != CREDIT_CLASS:
        failures.append("kill cell fixture/credit class drift")
    if cell.get("real_outcomes") != 0 or cell.get("parity_credit") != 0:
        failures.append("kill cell cannot claim real or parity credit")
    return failures


def validate_evidence_root(
    evidence_root: Path,
    *,
    expected_worker_sha256: str | None = None,
    expected_primitive_sha256: str | None = None,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    if evidence_root.is_symlink() or not evidence_root.is_dir():
        raise StoreEvidenceError("store evidence root must be a real directory")
    storage_path = evidence_root / "storage-classes.json"
    if storage_path.is_symlink() or not storage_path.is_file():
        raise StoreEvidenceError("storage-classes evidence must be a real file")
    storage_document = load_canonical(storage_path)
    storage_fields = {
        "schema",
        "storage_classes",
        "baseline_projection_sha256",
        "process_interruption_only",
        "power_loss_proven",
        "record_sha256",
    }
    if not isinstance(storage_document, dict) or set(storage_document) != storage_fields:
        raise StoreEvidenceError("storage-classes fields must be exact")
    expected_storage_hash = domain_digest(
        STORAGE_CLASSES_SCHEMA,
        {key: value for key, value in storage_document.items() if key != "record_sha256"},
    )
    if storage_document.get("schema") != STORAGE_CLASSES_SCHEMA or storage_document.get("record_sha256") != expected_storage_hash:
        raise StoreEvidenceError("storage-classes identity drift")
    if storage_document.get("process_interruption_only") is not True or storage_document.get("power_loss_proven") is not False:
        raise StoreEvidenceError("storage-classes claim boundary drift")
    classes = storage_document.get("storage_classes")
    if not isinstance(classes, list) or [item.get("id") for item in classes] != list(STORAGE_CLASS_IDS):
        raise StoreEvidenceError("storage class order/population drift")
    for descriptor in classes:
        failures = validate_storage_descriptor(descriptor)
        if failures:
            raise StoreEvidenceError("; ".join(failures))
    baselines = storage_document.get("baseline_projection_sha256")
    if (
        not isinstance(baselines, dict)
        or list(baselines) != list(STORAGE_CLASS_IDS)
        or not all(HEX64.fullmatch(str(value)) for value in baselines.values())
    ):
        raise StoreEvidenceError("storage baseline identity drift")
    expected_ids = [
        _cell_id(class_id, target_role, phase)
        for class_id in STORAGE_CLASS_IDS
        for target_role in TARGET_ROLES
        for phase in PHASES
    ]
    actual_entries = sorted(path.name for path in evidence_root.iterdir())
    if actual_entries != sorted(["storage-classes.json", *expected_ids]):
        raise StoreEvidenceError("retained store evidence population drift")
    cells = []
    for control_id in expected_ids:
        directory = evidence_root / control_id
        if not directory.is_dir() or directory.is_symlink():
            raise StoreEvidenceError(f"kill cell directory missing: {control_id}")
        entries = list(directory.iterdir())
        if sorted(path.name for path in entries) != ["cell.json", "marker.bin", "stderr.bin", "stdout.bin"]:
            raise StoreEvidenceError(f"kill cell file population drift: {control_id}")
        if any(path.is_symlink() or not path.is_file() for path in entries):
            raise StoreEvidenceError(f"kill cell contains a non-file or symlink: {control_id}")
        cell = load_canonical(directory / "cell.json")
        failures = validate_cell(
            cell,
            storage_document=storage_document,
            evidence_directory=directory,
            expected_worker_sha256=expected_worker_sha256,
            expected_primitive_sha256=expected_primitive_sha256,
        )
        if failures:
            raise StoreEvidenceError(f"{control_id}: {'; '.join(failures)}")
        cells.append(cell)
    return storage_document, cells


def _evidence_manifest(evidence_root: Path) -> list[dict[str, Any]]:
    return [
        {
            "path": path.relative_to(ROOT).as_posix(),
            "bytes": path.stat().st_size,
            "sha256": sha256_file(path),
        }
        for path in sorted(item for item in evidence_root.rglob("*") if item.is_file())
    ]


def validate_implementation_revision(
    implementation_revision: str, source_paths: list[Path]
) -> None:
    if not HEX40.fullmatch(implementation_revision):
        raise StoreEvidenceError("implementation revision must be lowercase 40-hex")
    git = shutil.which("git")
    if git is None:
        raise StoreEvidenceError("git is required to validate the implementation revision")
    git = os.path.realpath(git)
    try:
        ancestry = subprocess.run(
            [git, "merge-base", "--is-ancestor", implementation_revision, "HEAD"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise StoreEvidenceError("implementation revision ancestry check failed") from exc
    if ancestry.returncode != 0:
        raise StoreEvidenceError("implementation revision is not an ancestor of HEAD")
    for path in source_paths:
        relative = path.resolve().relative_to(ROOT).as_posix()
        try:
            committed = subprocess.run(
                [git, "show", f"{implementation_revision}:{relative}"],
                cwd=ROOT,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
                timeout=10,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise StoreEvidenceError(
                f"implementation revision source check failed: {relative}"
            ) from exc
        if committed.returncode != 0 or committed.stdout != path.read_bytes():
            raise StoreEvidenceError(
                f"implementation revision does not freeze current source: {relative}"
            )


def validate_historical_result_revision(implementation_revision: str) -> None:
    """Verify the retained source identities directly in their recorded revision."""
    if not HEX40.fullmatch(implementation_revision):
        raise StoreEvidenceError("implementation revision must be lowercase 40-hex")
    git = shutil.which("git")
    if git is None:
        raise StoreEvidenceError("git is required to validate the implementation revision")
    git = os.path.realpath(git)
    ancestry = subprocess.run(
        [git, "merge-base", "--is-ancestor", implementation_revision, "HEAD"],
        cwd=ROOT,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=10,
    )
    if ancestry.returncode != 0:
        raise StoreEvidenceError("implementation revision is not an ancestor of HEAD")
    for source in HISTORICAL_RESULT_SOURCE_INPUTS:
        committed = subprocess.run(
            [git, "show", f"{implementation_revision}:{source['path']}"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=10,
        )
        if (
            committed.returncode != 0
            or sha256_bytes(committed.stdout) != source["sha256"]
        ):
            raise StoreEvidenceError(
                "implementation revision source identity drift: " + source["path"]
            )


def result_source_paths() -> list[Path]:
    return [
        PREREGISTRATION_PLAN,
        Path(__file__).resolve(),
        ROOT / "scripts/tests/test_lean_execution_store.py",
        PRIMITIVE,
        WORKER,
        ROOT / "scripts/gen-lean-execution-evidence.py",
        ROOT / "docs/plan/lean-execution-evidence-v1.json",
        ROOT / "docs/plan/lean-execution-process-v1.json",
    ]


def result_source_inputs(implementation_revision: str) -> list[dict[str, str]]:
    """Select immutable historical rows or a newly frozen current revision."""
    if implementation_revision == HISTORICAL_IMPLEMENTATION_REVISION:
        validate_historical_result_revision(implementation_revision)
        return copy.deepcopy(list(HISTORICAL_RESULT_SOURCE_INPUTS))
    source_paths = result_source_paths()
    validate_implementation_revision(implementation_revision, source_paths)
    return [
        {"path": path.relative_to(ROOT).as_posix(), "sha256": sha256_file(path)}
        for path in source_paths
    ]


def build_result_authority(evidence_root: Path, *, implementation_revision: str) -> dict[str, Any]:
    evidence_root = evidence_root.resolve()
    try:
        relative_evidence_root = evidence_root.relative_to(ROOT).as_posix()
    except ValueError as exc:
        raise StoreEvidenceError("store evidence root must be inside repository") from exc
    source_inputs = result_source_inputs(implementation_revision)
    source_hashes = {row["path"]: row["sha256"] for row in source_inputs}
    storage_document, cells = validate_evidence_root(
        evidence_root,
        expected_worker_sha256=source_hashes[
            WORKER.relative_to(ROOT).as_posix()
        ],
        expected_primitive_sha256=source_hashes[
            PRIMITIVE.relative_to(ROOT).as_posix()
        ],
    )
    evidence_files = _evidence_manifest(evidence_root)
    phase_counts = Counter(cell["phase"] for cell in cells)
    target_counts = Counter(cell["target_role"] for cell in cells)
    class_counts = Counter(cell["storage_class_id"] for cell in cells)
    resume_counts = Counter(cell["resume_outcome"] for cell in cells)
    authority: dict[str, Any] = {
        "schema": RESULT_SCHEMA,
        "as_of": "2026-07-22",
        "scope": "synthetic-local-process-interruption-store-controls-no-power-loss-lean-u2-or-parity-credit",
        "preregistration": {
            "plan_commit": PREREGISTRATION_COMMIT,
            "plan_sha256": sha256_file(PREREGISTRATION_PLAN),
            "implementation_revision": implementation_revision,
            "plan_published_before_implementation": True,
            "implementation_published_before_kill_matrix": True,
        },
        "source_inputs": source_inputs,
        "evidence_root": relative_evidence_root,
        "evidence_files": evidence_files,
        "storage_classes": storage_document["storage_classes"],
        "baseline_projection_sha256": storage_document["baseline_projection_sha256"],
        "cells": cells,
        "summary": {
            "storage_classes": len(storage_document["storage_classes"]),
            "uninterrupted_baselines": len(storage_document["baseline_projection_sha256"]),
            "kill_cells": len(cells),
            "phase_counts": dict(phase_counts),
            "target_counts": dict(target_counts),
            "storage_class_counts": dict(class_counts),
            "sigkill_cells": sum(cell["process"]["signal"] == signal.SIGKILL for cell in cells),
            "projection_equal_cells": sum(cell["canonical_projection_sha256"] == cell["baseline_projection_sha256"] for cell in cells),
            "resume_outcome_counts": dict(resume_counts),
            "orphan_cells": sum(cell["orphan_count"] > 0 for cell in cells),
            "evidence_files": len(evidence_files),
            "evidence_bytes": sum(row["bytes"] for row in evidence_files),
            "real_outcomes": 0,
            "completed_u2_cases": 0,
            "paired_cells": 0,
            "performance_rows": 0,
            "parity_credit": 0,
        },
        "claims": {
            "atomic_no_replace_local": True,
            "process_sigkill_recovery": True,
            "completion_last_closure": True,
            "power_loss_recovery": False,
            "host_loss_recovery": False,
            "network_or_object_durability": False,
            "official_or_axeyum_execution": False,
        },
        "milestones": [
            {"id": "TL0.7.1", "state": "done"},
            {"id": "TL0.7.2", "state": "done"},
            {"id": "TL0.7.3", "state": "local-process-interruption-controls-complete"},
            {"id": "TL0.7.4", "state": "not-run"},
            {"id": "TL0.6.3", "state": "blocked-on-tl0.7"},
        ],
        "residual": [
            "Run one pinned-Lean preflight and one official-export control through this store with zero U2/parity credit in TL0.7.4.",
            "Do not generalize local process SIGKILL evidence to power loss, host loss, NFS, provider artifacts, or distributed durability.",
            "Keep TL0.6.3 blocked until TL0.7.4 accepts or revises the complete policy.",
        ],
        "authority_sha256": "",
    }
    authority["authority_sha256"] = domain_digest(
        RESULT_SCHEMA,
        {key: value for key, value in authority.items() if key != "authority_sha256"},
    )
    return authority


def validate_result_authority(authority: Any) -> list[str]:
    if not isinstance(authority, dict):
        return ["store result authority must be an object"]
    preregistration = authority.get("preregistration")
    evidence_root = authority.get("evidence_root")
    if not isinstance(preregistration, dict) or not isinstance(evidence_root, str):
        return ["store result authority identity fields missing"]
    try:
        expected = build_result_authority(
            ROOT / evidence_root,
            implementation_revision=str(preregistration.get("implementation_revision")),
        )
    except StoreEvidenceError as exc:
        return [str(exc)]
    return [] if authority == expected else ["store result authority differs from retained evidence"]


def build_summary(authority: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": SUMMARY_SCHEMA,
        "authority_sha256": authority["authority_sha256"],
        "scope": authority["scope"],
        "summary": authority["summary"],
        "claims": authority["claims"],
        "storage_classes": authority["storage_classes"],
        "cells": authority["cells"],
        "milestones": authority["milestones"],
        "residual": authority["residual"],
    }


def render_markdown(authority: dict[str, Any]) -> str:
    summary = authority["summary"]
    lines = [
        "# Generated TL0.7.3 Lean checkpoint-store result",
        "",
        "> Generated by `scripts/lean_execution_store.py`; do not hand-edit.",
        "",
        "This is synthetic local process-interruption evidence. It is not power-loss,",
        "host-loss, network/object-storage, Lean/U2 execution, or parity evidence.",
        "",
        "## Summary",
        "",
        f"- Storage classes / uninterrupted baselines: **{summary['storage_classes']} / {summary['uninterrupted_baselines']}**",
        f"- Reaped SIGKILL cells: **{summary['sigkill_cells']}/{summary['kill_cells']}**",
        f"- Canonical projection equality: **{summary['projection_equal_cells']}/{summary['kill_cells']}**",
        f"- Resume outcomes: **installed={summary['resume_outcome_counts'].get('installed', 0)}**, **existing-valid={summary['resume_outcome_counts'].get('existing-valid', 0)}**",
        f"- Cells with quarantined orphan temporaries: **{summary['orphan_cells']}**",
        f"- Retained files/bytes: **{summary['evidence_files']} / {summary['evidence_bytes']}**",
        "- Real outcomes / completed U2 cases / paired cells / parity credit: **0 / 0 / 0 / 0**",
        "",
        "## Matrix",
        "",
        "| Cell | Storage | Target | Phase | Signal | Orphans | Resume | Projection |",
        "|---|---|---|---|---:|---:|---|---|",
    ]
    for cell in authority["cells"]:
        lines.append(
            f"| `{cell['control_id']}` | `{cell['storage_class_id']}` | `{cell['target_role']}` | "
            f"`{cell['phase']}` | {cell['process']['signal']} | {cell['orphan_count']} | "
            f"`{cell['resume_outcome']}` | equal |"
        )
    lines.extend(
        [
            "",
            "## Residual",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in authority["residual"])
    return "\n".join(lines) + "\n"


def generate_result(*, evidence_root: Path, implementation_revision: str | None, check: bool) -> None:
    if check:
        try:
            authority = json.loads(RESULT_AUTHORITY.read_bytes())
        except (OSError, json.JSONDecodeError) as exc:
            raise StoreEvidenceError("cannot read committed store result authority") from exc
        failures = validate_result_authority(authority)
        if failures:
            raise StoreEvidenceError("; ".join(failures))
    else:
        if implementation_revision is None:
            raise StoreEvidenceError("result generation requires --implementation-revision")
        authority = build_result_authority(
            evidence_root, implementation_revision=implementation_revision
        )
    summary = build_summary(authority)
    outputs = {
        RESULT_AUTHORITY: json.dumps(authority, indent=2) + "\n",
        RESULT_JSON: json.dumps(summary, indent=2) + "\n",
        RESULT_MARKDOWN: render_markdown(authority),
    }
    if check:
        stale = [path for path, content in outputs.items() if not path.is_file() or path.read_text() != content]
        if stale:
            raise StoreEvidenceError(
                "stale store result: " + ", ".join(path.relative_to(ROOT).as_posix() for path in stale)
            )
    else:
        for path, content in outputs.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print(
        "LEAN_STORE_RESULT|"
        f"classes={summary['summary']['storage_classes']}|"
        f"kill_cells={summary['summary']['kill_cells']}|"
        f"projection_equal={summary['summary']['projection_equal_cells']}|"
        "real_outcomes=0|paired_cells=0|parity_credit=0"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    matrix = subparsers.add_parser("run-matrix")
    matrix.add_argument("--output-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    matrix.add_argument("--worktree-parent", type=Path, default=ROOT)
    matrix.add_argument("--tmpfs-parent", type=Path, default=Path("/dev/shm"))
    result = subparsers.add_parser("result")
    result.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    result.add_argument("--implementation-revision")
    result.add_argument("--check", action="store_true")
    validate = subparsers.add_parser("validate-store")
    validate.add_argument("--root", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.command == "run-matrix":
            run_matrix(
                output_root=args.output_root,
                worktree_parent=args.worktree_parent,
                tmpfs_parent=args.tmpfs_parent,
            )
        elif args.command == "result":
            generate_result(
                evidence_root=args.evidence_root,
                implementation_revision=args.implementation_revision,
                check=args.check,
            )
        elif args.command == "validate-store":
            projection = validate_complete_store(args.root)
            print(f"LEAN_STORE_VALID|projection_sha256={sha256_bytes(projection)}|credit=zero")
        else:  # pragma: no cover
            raise AssertionError(args.command)
    except (StoreEvidenceError, CheckpointConflict) as exc:
        print(f"LEAN_STORE_ERROR|{exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
