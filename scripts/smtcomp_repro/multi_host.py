"""E3 multi-host orchestration and shared-NFS evidence.

The module deliberately keeps remote execution untrusted.  A coordinator
preallocates host/shard ownership in a canonical plan, each host still runs the
E2 cgroup adapter, and central export requires complete E1/E2/E3 evidence.
"""

from __future__ import annotations

import argparse
import copy
import errno
import json
import os
import platform
import re
import signal
import socket
import stat
import subprocess
import sys
import time
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable

from resume_contract import (
    ATTEMPT_TERMINAL_FIELDS,
    ContractError,
    canonical_bytes,
    digest,
    merge_complete,
    record_set_sha256,
)
from resume_fs import (
    atomic_install_bytes,
    atomic_install_json,
    load_bundle,
    read_canonical_json,
    recover_shard_lease,
    verify_output_sidecars,
)
from resource_enforcement import (
    MULTI_HOST_KIND,
    build_resource_completion,
    install_resource_completion,
    validate_resource_evidence,
    validate_resource_session,
)
from resume_runner import (
    RUNNER_SOURCE_NAMES,
    sha256_bytes,
    sha256_file,
    source_identity_artifact,
    toolchain_identity_sha256,
    validate_source_identity,
)


TRANSPORT = "shared-nfs-v4.1-atomic-link-v1"
PLAN_SCHEMA = "axeyum.smtcomp-multi-host-plan.v1"
OBSERVATION_SCHEMA = "axeyum.smtcomp-host-observation.v1"
ENVIRONMENT_SCHEMA = "axeyum.smtcomp-multi-host-environment.v1"
REGISTRATION_SCHEMA = "axeyum.smtcomp-host-registration.v1"
ALLOCATION_SCHEMA = "axeyum.smtcomp-host-allocation.v1"
BUNDLE_SCHEMA = "axeyum.smtcomp-execution-bundle.v1"
COMMAND_SCHEMA = "axeyum.smtcomp-host-command.v1"
ATTEMPT_SCHEMA = "axeyum.smtcomp-host-allocation-attempt.v1"
TERMINAL_SCHEMA = "axeyum.smtcomp-host-allocation-terminal.v1"
RECOVERY_SCHEMA = "axeyum.smtcomp-host-recovery.v1"
RELEASED_RECOVERY_SCHEMA = "axeyum.smtcomp-host-released-recovery.v1"
FAULT_SCHEMA = "axeyum.smtcomp-host-fault-observation.v1"
COMPLETION_SCHEMA = "axeyum.smtcomp-multi-host-completion.v1"
POST_RUN_CLOSURE_SCHEMA = "axeyum.smtcomp-post-run-validation-closure.v1"
POST_RUN_COMPLETION_SCHEMA = "axeyum.smtcomp-multi-host-completion.v2"

SAFE_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}\Z")
SAFE_SSH_TARGET = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.@-]{0,127}\Z")
SAFE_PATH = re.compile(r"/[A-Za-z0-9_./-]+\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
PLAN_FIELDS = {
    "schema",
    "run_identity_sha256",
    "transport",
    "shared_root",
    "shared_filesystem_class_sha256",
    "environment_class_sha256",
    "host_registrations",
    "allocations",
    "fault_injection",
    "plan_sha256",
}
OBSERVATION_FIELDS = {
    "schema",
    "hostname",
    "kernel_release",
    "machine",
    "python_version",
    "python_executable_sha256",
    "toolchain_identity_sha256",
    "cgroup_controllers",
    "user_systemd_transient",
    "shared_filesystem",
    "shared_filesystem_class_sha256",
    "record_sha256",
}
REGISTRATION_FIELDS = {
    "schema",
    "host_id",
    "ssh_target",
    "hostname",
    "kernel_release",
    "machine",
    "python_version",
    "python_executable_sha256",
    "toolchain_identity_sha256",
    "cgroup_controllers",
    "user_systemd_transient",
    "shared_filesystem_class_sha256",
    "environment_class_sha256",
    "record_sha256",
}
ALLOCATION_FIELDS = {
    "schema",
    "allocation_id",
    "generation",
    "host_id",
    "shard_ids",
    "enforcement_id",
    "recovers_allocation_id",
    "record_sha256",
}
COMMAND_FIELDS = {
    "schema",
    "plan_sha256",
    "run_identity_sha256",
    "allocation_id",
    "host_id",
    "session_id",
    "plan_path",
    "run_manifest_path",
    "remote_helper_path",
    "remote_helper_sha256",
    "argv",
    "argv_sha256",
    "record_sha256",
}
ATTEMPT_FIELDS = {
    "schema",
    "plan_sha256",
    "run_identity_sha256",
    "allocation_id",
    "attempt_id",
    "host_id",
    "session_id",
    "command_sha256",
    "coordinator_host",
    "coordinator_pid",
    "started_at_ns",
    "record_sha256",
}
TERMINAL_FIELDS = {
    "schema",
    "attempt_id",
    "status",
    "exit_code",
    "stdout_sha256",
    "stdout_bytes",
    "stderr_sha256",
    "stderr_bytes",
    "ended_at_ns",
    "record_sha256",
}
RECOVERY_FIELDS = {
    "schema",
    "plan_sha256",
    "run_identity_sha256",
    "failed_allocation_id",
    "retry_allocation_id",
    "resource_session_id",
    "shard_id",
    "lease_owner_id",
    "remote_unit",
    "remote_unit_state",
    "launcher_pid",
    "launcher_live",
    "observed_at_ns",
    "quarantine_path",
    "record_sha256",
}
RELEASED_RECOVERY_FIELDS = {
    "schema",
    "plan_sha256",
    "run_identity_sha256",
    "failed_allocation_id",
    "retry_allocation_id",
    "resource_session_id",
    "shard_id",
    "failed_attempt_id",
    "failed_terminal_record_sha256",
    "runner_terminal_path",
    "runner_terminal_sha256",
    "resource_terminal_record_sha256",
    "resource_terminal_sha256",
    "lease_state",
    "remote_unit",
    "remote_unit_state",
    "launcher_pid",
    "launcher_live",
    "observed_at_ns",
    "record_sha256",
}
FAULT_FIELDS = {
    "schema",
    "plan_sha256",
    "run_identity_sha256",
    "allocation_id",
    "resource_session_id",
    "marker_path",
    "marker_sha256",
    "marker_bytes",
    "marker_content_hex",
    "marker_mtime_ns",
    "remote_unit",
    "launcher_pid",
    "cgroup_path",
    "signal",
    "killed_at_ns",
    "record_sha256",
}
COMPLETION_FIELDS = {
    "schema",
    "plan_sha256",
    "run_identity_sha256",
    "allocation_attempt_ids",
    "unclosed_allocation_attempt_ids",
    "recovery_record_sha256s",
    "resource_session_ids",
    "canonical_bundle_sha256",
    "resource_completion_sha256",
    "fault_record_sha256",
    "completed_at_ns",
    "record_sha256",
}
POST_RUN_COMPLETION_FIELDS = COMPLETION_FIELDS | {
    "post_run_closure_record_sha256s",
}
POST_RUN_CLOSURE_FIELDS = {
    "schema",
    "plan_sha256",
    "run_identity_sha256",
    "recovery_record_sha256",
    "allocation_id",
    "allocation_attempt_id",
    "allocation_attempt_sha256",
    "allocation_attempt_record_sha256",
    "allocation_terminal_sha256",
    "allocation_terminal_record_sha256",
    "resource_session_id",
    "resource_preflight_sha256",
    "resource_preflight_record_sha256",
    "resource_terminal_sha256",
    "resource_terminal_record_sha256",
    "shard_id",
    "runner_attempt_id",
    "runner_attempt_sha256",
    "runner_terminal_sha256",
    "shard_completion_sha256",
    "diagnostic_terminal_path",
    "diagnostic_terminal_sha256",
    "quarantine_path",
    "stderr_sha256",
    "error_class",
    "record_set_sha256",
    "canonical_bundle_sha256",
    "remote_unit",
    "remote_unit_state",
    "launcher_pid",
    "launcher_live",
    "observed_at_ns",
    "record_sha256",
}
RUN_DIRECTORIES = (
    "assignments",
    "attempts",
    "completions",
    "records",
    "terminals",
    "outputs",
    "outputs/stdout",
    "outputs/stderr",
    "leases",
    "quarantine",
    "resource-sessions",
    "multi-host-commands",
    "multi-host-attempts",
    "multi-host-terminals",
    "multi-host-outputs",
    "multi-host-outputs/stdout",
    "multi-host-outputs/stderr",
    "multi-host-recoveries",
)
FILESYSTEM_FIELDS = {
    "source",
    "filesystem_type",
    "mount_point",
    "options",
    "class_sha256",
}


def _sealed(value: dict[str, Any], hash_field: str = "record_sha256") -> dict[str, Any]:
    sealed = copy.deepcopy(value)
    sealed.pop(hash_field, None)
    sealed[hash_field] = digest(sealed)
    return sealed


def _validate_seal(value: dict[str, Any], hash_field: str = "record_sha256") -> None:
    unsealed = copy.deepcopy(value)
    claimed = unsealed.pop(hash_field, None)
    if claimed != digest(unsealed):
        raise ContractError(f"multi-host evidence hash mismatch: {hash_field}")


def _require_safe(value: Any, field: str, pattern: re.Pattern[str] = SAFE_ID) -> str:
    if not isinstance(value, str) or not pattern.fullmatch(value):
        raise ContractError(f"unsafe multi-host field: {field}")
    return value


def _require_sha(value: Any, field: str) -> str:
    if not isinstance(value, str) or not SHA256.fullmatch(value):
        raise ContractError(f"invalid SHA-256 field: {field}")
    return value


def _require_safe_absolute_path(value: Path | str, field: str) -> Path:
    raw = str(value)
    if not SAFE_PATH.fullmatch(raw) or not Path(raw).is_absolute():
        raise ContractError(f"unsafe absolute multi-host path: {field}")
    return Path(raw)


def _require_e3_unit(value: str) -> str:
    unit = _require_safe(value, "remote_unit")
    if not unit.startswith("axeyum-smtcomp-e3-") or not unit.endswith(".service"):
        raise ContractError("remote unit is outside the E3 namespace")
    return unit


def _decode_mount_path(value: str) -> str:
    return (
        value.replace("\\040", " ")
        .replace("\\011", "\t")
        .replace("\\012", "\n")
        .replace("\\134", "\\")
    )


def shared_filesystem_observation(shared_root: Path) -> dict[str, Any]:
    """Return the exact mount class for ``shared_root`` from mountinfo."""

    root = shared_root.resolve(strict=True)
    candidates: list[tuple[int, dict[str, Any]]] = []
    try:
        lines = Path("/proc/self/mountinfo").read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError) as exc:
        raise ContractError("cannot read mountinfo for E3 shared storage") from exc
    for line in lines:
        left, separator, right = line.partition(" - ")
        if not separator:
            continue
        left_fields = left.split()
        right_fields = right.split()
        if len(left_fields) < 6 or len(right_fields) < 3:
            continue
        mount_point = Path(_decode_mount_path(left_fields[4]))
        try:
            root.relative_to(mount_point)
        except ValueError:
            continue
        options = set(left_fields[5].split(",")) | set(right_fields[2].split(","))
        class_options = sorted(
            option
            for option in options
            if option and not option.startswith("clientaddr=")
        )
        candidates.append(
            (
                len(mount_point.parts),
                {
                    "source": right_fields[1],
                    "filesystem_type": right_fields[0],
                    "mount_point": str(mount_point),
                    "options": class_options,
                },
            )
        )
    if not candidates:
        raise ContractError("shared root has no mountinfo entry")
    observation = max(candidates, key=lambda item: item[0])[1]
    required_options = {"vers=4.1", "hard", "local_lock=none"}
    if (
        observation["filesystem_type"] != "nfs4"
        or not required_options <= set(observation["options"])
    ):
        raise ContractError("E3 requires the registered NFSv4.1 shared filesystem")
    observation["class_sha256"] = digest(observation)
    return observation


def local_host_observation(shared_root: Path, *, probe_systemd: bool = True) -> dict[str, Any]:
    filesystem = shared_filesystem_observation(shared_root)
    transient = False
    if probe_systemd:
        unit = f"axeyum-e3-probe-{os.getpid()}-{uuid.uuid4().hex[:8]}"
        try:
            completed = subprocess.run(
                [
                    "systemd-run",
                    "--user",
                    "--wait",
                    "--collect",
                    "--pipe",
                    f"--unit={unit}",
                    "--property=Type=exec",
                    "/usr/bin/true",
                ],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=10,
                check=False,
            )
            transient = completed.returncode == 0
        except (OSError, subprocess.TimeoutExpired):
            transient = False
    controllers = sorted(
        (Path("/sys/fs/cgroup") / "cgroup.controllers")
        .read_text(encoding="ascii")
        .split()
    )
    executable = Path(sys.executable).resolve()
    return _sealed(
        {
            "schema": OBSERVATION_SCHEMA,
            "hostname": socket.gethostname(),
            "kernel_release": platform.release(),
            "machine": platform.machine(),
            "python_version": platform.python_version(),
            "python_executable_sha256": sha256_file(executable),
            "toolchain_identity_sha256": toolchain_identity_sha256(),
            "cgroup_controllers": controllers,
            "user_systemd_transient": transient,
            "shared_filesystem": filesystem,
            "shared_filesystem_class_sha256": filesystem["class_sha256"],
        }
    )


def validate_host_observation(observation: dict[str, Any]) -> dict[str, Any]:
    if set(observation) != OBSERVATION_FIELDS:
        raise ContractError("host observation field set mismatch")
    if observation.get("schema") != OBSERVATION_SCHEMA:
        raise ContractError("host observation schema mismatch")
    _validate_seal(observation)
    _require_safe(observation.get("hostname"), "hostname")
    for field in (
        "kernel_release",
        "machine",
        "python_version",
    ):
        if not isinstance(observation.get(field), str) or not observation[field]:
            raise ContractError(f"invalid host observation field: {field}")
    for field in (
        "python_executable_sha256",
        "toolchain_identity_sha256",
        "shared_filesystem_class_sha256",
    ):
        _require_sha(observation.get(field), field)
    controllers = observation.get("cgroup_controllers")
    if (
        not isinstance(controllers, list)
        or controllers != sorted(set(controllers))
        or not {"cpu", "memory", "pids"} <= set(controllers)
    ):
        raise ContractError("host lacks required cgroup-v2 controllers")
    if observation.get("user_systemd_transient") is not True:
        raise ContractError("host lacks working user-systemd transient services")
    filesystem = observation.get("shared_filesystem")
    if (
        not isinstance(filesystem, dict)
        or set(filesystem) != FILESYSTEM_FIELDS
        or filesystem.get("filesystem_type") != "nfs4"
        or not isinstance(filesystem.get("source"), str)
        or not filesystem["source"]
        or not isinstance(filesystem.get("mount_point"), str)
        or not Path(filesystem["mount_point"]).is_absolute()
        or not isinstance(filesystem.get("options"), list)
        or filesystem["options"] != sorted(set(filesystem["options"]))
        or not {"vers=4.1", "hard", "local_lock=none"}
        <= set(filesystem["options"])
        or digest(
            {key: value for key, value in filesystem.items() if key != "class_sha256"}
        )
        != filesystem.get("class_sha256")
    ):
        raise ContractError("host shared-filesystem identity mismatch")
    if filesystem["class_sha256"] != observation["shared_filesystem_class_sha256"]:
        raise ContractError("host shared-filesystem class mismatch")
    return observation


def environment_manifest(observations: list[dict[str, Any]]) -> dict[str, Any]:
    if len(observations) < 3:
        raise ContractError("E3 environment registration requires at least three hosts")
    validated = [validate_host_observation(value) for value in observations]
    if len({value["hostname"] for value in validated}) != len(validated):
        raise ContractError("E3 environment registration contains duplicate hosts")
    common_fields = (
        "kernel_release",
        "machine",
        "python_version",
        "python_executable_sha256",
        "toolchain_identity_sha256",
        "cgroup_controllers",
        "user_systemd_transient",
        "shared_filesystem_class_sha256",
    )
    common = {field: validated[0][field] for field in common_fields}
    for observation in validated[1:]:
        if any(observation[field] != common[field] for field in common_fields):
            raise ContractError("E3 hosts are outside one registered environment class")
    return _sealed(
        {
            "schema": ENVIRONMENT_SCHEMA,
            "host_count": len(validated),
            "hostnames": sorted(value["hostname"] for value in validated),
            "shared_filesystem": validated[0]["shared_filesystem"],
            **common,
        }
    )


def host_registration(
    *, host_id: str, ssh_target: str, observation: dict[str, Any], environment_sha256: str
) -> dict[str, Any]:
    observed = validate_host_observation(observation)
    return _sealed(
        {
            "schema": REGISTRATION_SCHEMA,
            "host_id": _require_safe(host_id, "host_id"),
            "ssh_target": _require_safe(
                ssh_target, "ssh_target", pattern=SAFE_SSH_TARGET
            ),
            "hostname": observed["hostname"],
            "kernel_release": observed["kernel_release"],
            "machine": observed["machine"],
            "python_version": observed["python_version"],
            "python_executable_sha256": observed["python_executable_sha256"],
            "toolchain_identity_sha256": observed["toolchain_identity_sha256"],
            "cgroup_controllers": observed["cgroup_controllers"],
            "user_systemd_transient": observed["user_systemd_transient"],
            "shared_filesystem_class_sha256": observed[
                "shared_filesystem_class_sha256"
            ],
            "environment_class_sha256": _require_sha(
                environment_sha256, "environment_class_sha256"
            ),
        }
    )


def allocation(
    *,
    allocation_id: str,
    generation: int,
    host_id: str,
    shard_ids: list[int],
    enforcement_id: str,
    recovers_allocation_id: str | None = None,
) -> dict[str, Any]:
    return _sealed(
        {
            "schema": ALLOCATION_SCHEMA,
            "allocation_id": _require_safe(allocation_id, "allocation_id"),
            "generation": generation,
            "host_id": _require_safe(host_id, "host_id"),
            "shard_ids": shard_ids,
            "enforcement_id": _require_sha(enforcement_id, "enforcement_id"),
            "recovers_allocation_id": recovers_allocation_id,
        }
    )


def build_plan(
    *,
    run: dict[str, Any],
    shared_root: Path,
    environment_class_sha256: str,
    host_registrations: list[dict[str, Any]],
    allocations: list[dict[str, Any]],
    fault_injection: dict[str, Any] | None = None,
) -> dict[str, Any]:
    filesystem = shared_filesystem_observation(shared_root)
    plan = {
        "schema": PLAN_SCHEMA,
        "run_identity_sha256": run["identity_sha256"],
        "transport": TRANSPORT,
        "shared_root": str(shared_root.resolve(strict=True)),
        "shared_filesystem_class_sha256": filesystem["class_sha256"],
        "environment_class_sha256": environment_class_sha256,
        "host_registrations": host_registrations,
        "allocations": allocations,
        "fault_injection": fault_injection or {"kind": "none"},
    }
    plan["plan_sha256"] = digest(plan)
    return validate_plan(plan, run)


def validate_plan(
    plan: dict[str, Any], run: dict[str, Any], *, inspect_shared_root: bool = True
) -> dict[str, Any]:
    if set(plan) != PLAN_FIELDS or plan.get("schema") != PLAN_SCHEMA:
        raise ContractError("multi-host plan field/schema mismatch")
    _validate_seal(plan, "plan_sha256")
    if plan.get("run_identity_sha256") != run.get("identity_sha256"):
        raise ContractError("multi-host plan run identity mismatch")
    if run.get("resource_enforcement", {}).get("kind") != MULTI_HOST_KIND:
        raise ContractError("multi-host plan requires E3 enforcement")
    if plan.get("transport") != TRANSPORT:
        raise ContractError("unsupported multi-host transport")
    shared_root_raw = plan.get("shared_root")
    if not isinstance(shared_root_raw, str) or not Path(shared_root_raw).is_absolute():
        raise ContractError("multi-host shared root must be absolute")
    resolved_root = Path(shared_root_raw).resolve(strict=inspect_shared_root)
    if str(resolved_root) != shared_root_raw:
        raise ContractError("multi-host shared root must be canonical and non-symlinked")
    if inspect_shared_root:
        filesystem = shared_filesystem_observation(resolved_root)
        if filesystem["class_sha256"] != plan["shared_filesystem_class_sha256"]:
            raise ContractError("multi-host shared-filesystem drift")
    _require_sha(plan.get("environment_class_sha256"), "environment_class_sha256")
    _require_sha(
        plan.get("shared_filesystem_class_sha256"),
        "shared_filesystem_class_sha256",
    )

    registrations = plan.get("host_registrations")
    if not isinstance(registrations, list) or len(registrations) < 3:
        raise ContractError("multi-host plan requires at least three registrations")
    by_host: dict[str, dict[str, Any]] = {}
    hostnames: set[str] = set()
    targets: set[str] = set()
    for registration in registrations:
        if set(registration) != REGISTRATION_FIELDS:
            raise ContractError("host registration field set mismatch")
        if registration.get("schema") != REGISTRATION_SCHEMA:
            raise ContractError("host registration schema mismatch")
        _validate_seal(registration)
        host_id = _require_safe(registration.get("host_id"), "host_id")
        target = _require_safe(
            registration.get("ssh_target"), "ssh_target", pattern=SAFE_SSH_TARGET
        )
        hostname = _require_safe(registration.get("hostname"), "hostname")
        if host_id in by_host or hostname in hostnames or target in targets:
            raise ContractError("duplicate multi-host registration")
        if registration["environment_class_sha256"] != plan["environment_class_sha256"]:
            raise ContractError("host registration environment drift")
        if (
            registration["shared_filesystem_class_sha256"]
            != plan["shared_filesystem_class_sha256"]
        ):
            raise ContractError("host registration filesystem drift")
        for field in (
            "python_executable_sha256",
            "toolchain_identity_sha256",
            "shared_filesystem_class_sha256",
            "environment_class_sha256",
        ):
            _require_sha(registration.get(field), field)
        controllers = registration.get("cgroup_controllers")
        if (
            not isinstance(controllers, list)
            or controllers != sorted(set(controllers))
            or not {"cpu", "memory", "pids"} <= set(controllers)
            or registration.get("user_systemd_transient") is not True
        ):
            raise ContractError("host registration capability drift")
        by_host[host_id] = registration
        hostnames.add(hostname)
        targets.add(target)
    class_fields = (
        "kernel_release",
        "machine",
        "python_version",
        "python_executable_sha256",
        "toolchain_identity_sha256",
        "cgroup_controllers",
        "user_systemd_transient",
        "shared_filesystem_class_sha256",
        "environment_class_sha256",
    )
    baseline_registration = registrations[0]
    if any(
        registration[field] != baseline_registration[field]
        for registration in registrations[1:]
        for field in class_fields
    ):
        raise ContractError("host registrations are outside one environment class")

    allocation_rows = plan.get("allocations")
    if not isinstance(allocation_rows, list) or not allocation_rows:
        raise ContractError("multi-host plan has no allocations")
    by_allocation: dict[str, dict[str, Any]] = {}
    initial_shards: list[int] = []
    shard_count = run["identity"]["shard_count"]
    enforcement_id = run["resource_enforcement"]["enforcement_id"]
    for row in allocation_rows:
        if set(row) != ALLOCATION_FIELDS or row.get("schema") != ALLOCATION_SCHEMA:
            raise ContractError("host allocation field/schema mismatch")
        _validate_seal(row)
        allocation_id = _require_safe(row.get("allocation_id"), "allocation_id")
        if allocation_id in by_allocation:
            raise ContractError("duplicate host allocation")
        if row.get("host_id") not in by_host:
            raise ContractError("allocation names an unregistered host")
        generation = row.get("generation")
        shard_ids = row.get("shard_ids")
        if type(generation) is not int or generation < 0:
            raise ContractError("invalid allocation generation")
        if (
            not isinstance(shard_ids, list)
            or not shard_ids
            or shard_ids != sorted(set(shard_ids))
            or any(
                type(shard_id) is not int or not 0 <= shard_id < shard_count
                for shard_id in shard_ids
            )
        ):
            raise ContractError("invalid allocation shard set")
        if row.get("enforcement_id") != enforcement_id:
            raise ContractError("allocation enforcement drift")
        recovery = row.get("recovers_allocation_id")
        if generation == 0:
            if recovery is not None:
                raise ContractError("initial allocation cannot be a retry")
            initial_shards.extend(shard_ids)
        else:
            _require_safe(recovery, "recovers_allocation_id")
            failed = by_allocation.get(recovery)
            if failed is None or failed["generation"] >= generation:
                raise ContractError("retry allocation lacks an earlier owner")
            if len(shard_ids) != 1 or not set(shard_ids) <= set(failed["shard_ids"]):
                raise ContractError("retry allocation must recover one owned shard")
            if row["host_id"] == failed["host_id"]:
                raise ContractError("retry allocation must move to another host")
        by_allocation[allocation_id] = row
    if sorted(initial_shards) != list(range(shard_count)):
        raise ContractError("initial allocations do not partition every shard")
    if len(
        {
            row["host_id"]
            for row in allocation_rows
            if row["generation"] == 0
        }
    ) < 3:
        raise ContractError("initial allocations must exercise at least three hosts")
    fault = plan.get("fault_injection")
    if not isinstance(fault, dict) or fault.get("kind") not in {
        "none",
        "kill-host-runner-after-marker",
    }:
        raise ContractError("unsupported multi-host fault injection")
    if fault["kind"] != "none":
        if set(fault) != {"kind", "allocation_id", "marker_path"}:
            raise ContractError("fault injection field set mismatch")
        failed_id = _require_safe(fault.get("allocation_id"), "fault allocation_id")
        if failed_id not in by_allocation or by_allocation[failed_id]["generation"] != 0:
            raise ContractError("fault injection names a non-initial allocation")
        marker = fault.get("marker_path")
        if not isinstance(marker, str) or not SAFE_PATH.fullmatch(marker):
            raise ContractError("fault injection marker path is unsafe")
        try:
            Path(marker).parent.resolve().relative_to(Path(shared_root_raw).resolve())
        except ValueError as exc:
            raise ContractError("fault injection marker escapes the shared root") from exc
    elif set(fault) != {"kind"}:
        raise ContractError("none fault injection field set mismatch")
    return plan


def prepare_run_directory(
    *, plan: dict[str, Any], run: dict[str, Any], run_dir: Path
) -> None:
    """Create the exact shared namespace before concurrent hosts are launched."""

    validate_plan(plan, run)
    shared_root = Path(plan["shared_root"]).resolve(strict=True)
    resolved = run_dir.resolve()
    try:
        resolved.relative_to(shared_root)
    except ValueError as exc:
        raise ContractError("multi-host run directory escapes the shared root") from exc
    resolved.mkdir(mode=0o755, parents=True, exist_ok=True)
    for relative in RUN_DIRECTORIES:
        directory = resolved / relative
        directory.mkdir(mode=0o755, parents=True, exist_ok=True)
        if directory.is_symlink() or not directory.is_dir():
            raise ContractError(f"invalid prepared multi-host directory: {relative}")


def stage_execution_bundle(
    *,
    repository_root: Path,
    source_root: Path,
    fixture_root: Path,
    staging_parent: Path,
) -> tuple[Path, dict[str, Any]]:
    """Install a content-addressed runner/fixture bundle on shared storage."""

    source_identity = source_identity_artifact(repository_root, source_root)
    entries: list[tuple[str, Path]] = [
        (f"scripts/smtcomp_repro/{name}", source_root / name)
        for name in RUNNER_SOURCE_NAMES
    ]
    for path in sorted(fixture_root.rglob("*")):
        if path.is_file() and "__pycache__" not in path.parts:
            entries.append(
                (
                    f"scripts/smtcomp_repro/fixtures/e3/{path.relative_to(fixture_root)}",
                    path,
                )
            )
    file_rows = [
        {
            "path": relative,
            "sha256": sha256_file(path),
            "bytes": path.stat().st_size,
        }
        for relative, path in entries
    ]
    bundle_id = digest(
        {
            "schema": BUNDLE_SCHEMA,
            "source_identity_sha256": source_identity["record_sha256"],
            "files": file_rows,
        }
    )
    bundle_root = staging_parent.resolve(strict=True) / bundle_id
    bundle_root.mkdir(mode=0o755, exist_ok=True)
    quarantine = bundle_root / "quarantine"
    for relative, source in entries:
        destination = bundle_root / relative
        atomic_install_bytes(
            destination.parent,
            destination.name,
            source.read_bytes(),
            quarantine_root=quarantine,
        )
    atomic_install_json(
        bundle_root,
        "source-identity.json",
        source_identity,
        quarantine_root=quarantine,
    )
    completion = _sealed(
        {
            "schema": BUNDLE_SCHEMA,
            "bundle_id": bundle_id,
            "source_identity_sha256": source_identity["record_sha256"],
            "files": file_rows,
        }
    )
    atomic_install_json(
        bundle_root,
        "bundle-completion.json",
        completion,
        quarantine_root=quarantine,
    )
    validate_execution_bundle(bundle_root)
    return bundle_root, source_identity


def validate_execution_bundle(bundle_root: Path) -> dict[str, Any]:
    completion = read_canonical_json(bundle_root / "bundle-completion.json")
    if completion.get("schema") != BUNDLE_SCHEMA:
        raise ContractError("execution bundle schema mismatch")
    _validate_seal(completion)
    if bundle_root.name != completion.get("bundle_id"):
        raise ContractError("execution bundle directory identity mismatch")
    source_identity = read_canonical_json(bundle_root / "source-identity.json")
    validate_source_identity(
        source_identity, bundle_root / "scripts" / "smtcomp_repro"
    )
    if source_identity.get("record_sha256") != completion.get(
        "source_identity_sha256"
    ):
        raise ContractError("execution bundle source identity mismatch")
    rows = completion.get("files")
    if not isinstance(rows, list) or not rows:
        raise ContractError("execution bundle file ledger mismatch")
    expected_paths: set[str] = set()
    for row in rows:
        if (
            not isinstance(row, dict)
            or set(row) != {"path", "sha256", "bytes"}
            or not isinstance(row.get("path"), str)
            or Path(row["path"]).is_absolute()
            or any(part in {"", ".", ".."} for part in Path(row["path"]).parts)
            or type(row.get("bytes")) is not int
            or row["bytes"] < 0
        ):
            raise ContractError("execution bundle file ledger mismatch")
        _require_sha(row.get("sha256"), "bundle file sha256")
        expected_paths.add(row["path"])
    if len(expected_paths) != len(rows):
        raise ContractError("execution bundle file ledger mismatch")
    for row in completion["files"]:
        path = bundle_root / row["path"]
        if (
            not path.is_file()
            or path.is_symlink()
            or stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != row["bytes"]
            or sha256_file(path) != row["sha256"]
        ):
            raise ContractError(f"execution bundle file mismatch: {row['path']}")
    present = {
        str(path.relative_to(bundle_root))
        for path in bundle_root.rglob("*")
        if path.is_file() and "quarantine" not in path.relative_to(bundle_root).parts
    }
    expected = expected_paths | {"source-identity.json", "bundle-completion.json"}
    if present != expected:
        raise ContractError("execution bundle namespace mismatch")
    for name in ("source-identity.json", "bundle-completion.json"):
        if stat.S_IMODE((bundle_root / name).stat().st_mode) != 0o444:
            raise ContractError("execution bundle metadata is not immutable")
    return completion


def _option_value(argv: list[str], option: str) -> str:
    values: list[str] = []
    for index, token in enumerate(argv):
        if token == option:
            if index + 1 >= len(argv):
                raise ContractError(f"host command option lacks value: {option}")
            values.append(argv[index + 1])
        elif token.startswith(f"{option}="):
            values.append(token.split("=", 1)[1])
    if len(values) != 1:
        raise ContractError(f"host command must name {option} exactly once")
    return values[0]


def build_host_command(
    *,
    plan_path: Path,
    run_manifest_path: Path,
    allocation_id: str,
    session_id: str,
    remote_helper_path: Path,
    argv: list[str],
    inspect_shared_root: bool = True,
) -> dict[str, Any]:
    plan = read_canonical_json(plan_path)
    run = read_canonical_json(run_manifest_path)
    validate_plan(plan, run, inspect_shared_root=inspect_shared_root)
    by_allocation = {row["allocation_id"]: row for row in plan["allocations"]}
    allocation_row = by_allocation.get(allocation_id)
    if allocation_row is None:
        raise ContractError("host command names an unknown allocation")
    command = {
        "schema": COMMAND_SCHEMA,
        "plan_sha256": plan["plan_sha256"],
        "run_identity_sha256": run["identity_sha256"],
        "allocation_id": allocation_id,
        "host_id": allocation_row["host_id"],
        "session_id": _require_safe(session_id, "session_id"),
        "plan_path": str(plan_path.resolve(strict=True)),
        "run_manifest_path": str(run_manifest_path.resolve(strict=True)),
        "remote_helper_path": str(remote_helper_path.resolve(strict=True)),
        "remote_helper_sha256": sha256_file(remote_helper_path),
        "argv": argv,
        "argv_sha256": digest(argv),
    }
    return _sealed(command)


def validate_host_command(
    command: dict[str, Any], *, require_local_hostname: bool = False,
    inspect_shared_root: bool = True,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    if set(command) != COMMAND_FIELDS or command.get("schema") != COMMAND_SCHEMA:
        raise ContractError("host command field/schema mismatch")
    _validate_seal(command)
    for field in (
        "plan_sha256",
        "run_identity_sha256",
        "remote_helper_sha256",
        "argv_sha256",
    ):
        _require_sha(command.get(field), field)
    for field in ("allocation_id", "host_id", "session_id"):
        _require_safe(command.get(field), field)
    paths = {}
    for field in ("plan_path", "run_manifest_path", "remote_helper_path"):
        raw = command.get(field)
        if (
            not isinstance(raw, str)
            or not SAFE_PATH.fullmatch(raw)
            or not Path(raw).is_absolute()
        ):
            raise ContractError(f"host command path must be absolute: {field}")
        paths[field] = Path(raw)
    if sha256_file(paths["remote_helper_path"]) != command["remote_helper_sha256"]:
        raise ContractError("remote helper content drift")
    plan = read_canonical_json(paths["plan_path"])
    run = read_canonical_json(paths["run_manifest_path"])
    validate_plan(plan, run, inspect_shared_root=inspect_shared_root)
    if plan["plan_sha256"] != command["plan_sha256"]:
        raise ContractError("host command plan drift")
    if run["identity_sha256"] != command["run_identity_sha256"]:
        raise ContractError("host command run drift")
    allocations = {row["allocation_id"]: row for row in plan["allocations"]}
    allocation_row = allocations.get(command["allocation_id"])
    if allocation_row is None or allocation_row["host_id"] != command["host_id"]:
        raise ContractError("host command allocation drift")
    registrations = {row["host_id"]: row for row in plan["host_registrations"]}
    registration = registrations[command["host_id"]]
    if require_local_hostname and socket.gethostname() != registration["hostname"]:
        raise ContractError("host command reached the wrong hostname")
    argv = command.get("argv")
    if (
        not isinstance(argv, list)
        or not argv
        or any(
            not isinstance(token, str) or not token or "\0" in token or "\n" in token
            for token in argv
        )
        or digest(argv) != command["argv_sha256"]
    ):
        raise ContractError("host command argv identity mismatch")
    if len(argv) < 2 or "--host-run" not in argv:
        raise ContractError("host command does not activate aggregate execution")
    expected_shards = ",".join(str(value) for value in allocation_row["shard_ids"])
    exact_options = {
        "--host-shards": expected_shards,
        "--host-session-id": command["session_id"],
        "--run-manifest": str(paths["run_manifest_path"]),
    }
    for option, expected in exact_options.items():
        if _option_value(argv, option) != expected:
            raise ContractError(f"host command allocation option drift: {option}")
    run_dir = Path(_option_value(argv, "--run-dir"))
    shared_root = Path(plan["shared_root"]).resolve()
    try:
        run_dir.resolve().relative_to(shared_root)
    except ValueError as exc:
        raise ContractError("host command run directory escapes the shared root") from exc
    source_manifest = Path(_option_value(argv, "--source-identity-manifest"))
    if not source_manifest.is_absolute():
        raise ContractError("host command source identity path is not absolute")
    try:
        source_manifest.resolve().relative_to(shared_root)
    except ValueError as exc:
        raise ContractError("host command source identity escapes the shared root") from exc
    source = read_canonical_json(source_manifest)
    if len(argv) < 3 or argv[1] != "-B":
        raise ContractError("E3 host command must disable staged bytecode writes")
    source_root = Path(argv[2]).resolve().parent
    validate_source_identity(source, source_root)
    identity_fields = (
        "repository_commit",
        "source_tree_state_sha256",
        "runner_source_sha256",
    )
    if any(source[field] != run["identity"][field] for field in identity_fields):
        raise ContractError("host command source identity drift")
    for option in (
        "--file-list",
        "--selection-manifest",
        "--corpus-manifest",
        "--environment-manifest",
    ):
        path = Path(_option_value(argv, option))
        try:
            path.resolve().relative_to(shared_root)
        except ValueError as exc:
            raise ContractError(f"host command input escapes the shared root: {option}") from exc
    return plan, run, allocation_row


def install_host_command(run_dir: Path, command: dict[str, Any]) -> Path:
    allocation_id = command["allocation_id"]
    atomic_install_json(
        run_dir / "multi-host-commands",
        f"{allocation_id}.json",
        command,
        quarantine_root=run_dir / "quarantine",
    )
    return run_dir / "multi-host-commands" / f"{allocation_id}.json"


def build_fault_observation(
    *,
    plan: dict[str, Any],
    run: dict[str, Any],
    command: dict[str, Any],
    preflight: dict[str, Any],
    marker_observation: dict[str, Any],
    kill_observation: dict[str, Any],
) -> dict[str, Any]:
    """Bind the preregistered marker and exact launcher kill into evidence."""

    validate_plan(plan, run)
    fault = plan["fault_injection"]
    if fault["kind"] != "kill-host-runner-after-marker":
        raise ContractError("plan does not authorize a host fault observation")
    allocation_id = fault["allocation_id"]
    if (
        command.get("allocation_id") != allocation_id
        or command.get("session_id") != preflight.get("session_id")
        or preflight.get("launcher_pid") != kill_observation.get("launcher_pid")
        or marker_observation.get("path") != fault["marker_path"]
        or kill_observation.get("unit")
        != f"{run['resource_enforcement']['unit_prefix']}-{command['session_id']}.service"
    ):
        raise ContractError("fault observation ownership mismatch")
    return _sealed(
        {
            "schema": FAULT_SCHEMA,
            "plan_sha256": plan["plan_sha256"],
            "run_identity_sha256": run["identity_sha256"],
            "allocation_id": allocation_id,
            "resource_session_id": command["session_id"],
            "marker_path": marker_observation["path"],
            "marker_sha256": marker_observation["sha256"],
            "marker_bytes": marker_observation["bytes"],
            "marker_content_hex": marker_observation["content_hex"],
            "marker_mtime_ns": marker_observation["mtime_ns"],
            "remote_unit": kill_observation["unit"],
            "launcher_pid": kill_observation["launcher_pid"],
            "cgroup_path": kill_observation["cgroup_path"],
            "signal": kill_observation["signal"],
            "killed_at_ns": kill_observation["killed_at_ns"],
        }
    )


def install_fault_observation(run_dir: Path, record: dict[str, Any]) -> Path:
    atomic_install_json(
        run_dir,
        "multi-host-fault.json",
        record,
        quarantine_root=run_dir / "quarantine",
    )
    return run_dir / "multi-host-fault.json"


def execute_host_command(command_manifest: Path) -> int:
    command = read_canonical_json(command_manifest)
    validate_host_command(command, require_local_hostname=True)
    try:
        completed = subprocess.run(command["argv"], check=False)
    except OSError as exc:
        raise ContractError("unable to execute registered host command") from exc
    return completed.returncode


def remote_probe(
    *, ssh_target: str, remote_helper_path: Path, shared_root: Path
) -> dict[str, Any]:
    _require_safe(ssh_target, "ssh_target", pattern=SAFE_SSH_TARGET)
    helper = _require_safe_absolute_path(remote_helper_path, "remote_helper_path")
    root = _require_safe_absolute_path(shared_root, "shared_root")
    command = [
        "ssh",
        "-o",
        "BatchMode=yes",
        "-o",
        "ConnectTimeout=5",
        ssh_target,
        "python3",
        "-B",
        str(helper),
        "probe",
        "--shared-root",
        str(root),
    ]
    try:
        completed = subprocess.run(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=20,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ContractError(f"unable to probe E3 host: {ssh_target}") from exc
    if completed.returncode != 0:
        raise ContractError(
            f"E3 host probe failed: {ssh_target}: "
            f"{completed.stderr.decode('utf-8', errors='replace').strip()}"
        )
    try:
        observation = json.loads(completed.stdout)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError(f"E3 host returned malformed observation: {ssh_target}") from exc
    if completed.stdout != canonical_bytes(observation):
        raise ContractError(f"E3 host returned non-canonical observation: {ssh_target}")
    return validate_host_observation(observation)


@dataclass
class AllocationProcess:
    allocation_id: str
    attempt_id: str
    session_id: str
    process: subprocess.Popen[bytes]
    run_dir: Path
    launch: dict[str, Any]


def start_allocation(
    *, plan: dict[str, Any], command_manifest: Path, run_dir: Path
) -> AllocationProcess:
    command = read_canonical_json(command_manifest)
    _plan, run, allocation_row = validate_host_command(command)
    if _plan["plan_sha256"] != plan["plan_sha256"]:
        raise ContractError("allocation command uses a different plan")
    registrations = {row["host_id"]: row for row in plan["host_registrations"]}
    registration = registrations[allocation_row["host_id"]]
    expected_command_path = (
        run_dir / "multi-host-commands" / f"{allocation_row['allocation_id']}.json"
    ).resolve()
    if command_manifest.resolve(strict=True) != expected_command_path:
        raise ContractError("allocation command manifest is outside its exact run slot")
    _require_safe_absolute_path(expected_command_path, "command_manifest")
    attempt_id = (
        f"{allocation_row['allocation_id']}-{time.time_ns()}-{uuid.uuid4().hex[:12]}"
    )
    launch = _sealed(
        {
            "schema": ATTEMPT_SCHEMA,
            "plan_sha256": plan["plan_sha256"],
            "run_identity_sha256": run["identity_sha256"],
            "allocation_id": allocation_row["allocation_id"],
            "attempt_id": attempt_id,
            "host_id": allocation_row["host_id"],
            "session_id": command["session_id"],
            "command_sha256": command["record_sha256"],
            "coordinator_host": socket.gethostname(),
            "coordinator_pid": os.getpid(),
            "started_at_ns": time.time_ns(),
        }
    )
    atomic_install_json(
        run_dir / "multi-host-attempts" / allocation_row["allocation_id"],
        f"{attempt_id}.json",
        launch,
        quarantine_root=run_dir / "quarantine",
    )
    ssh_command = [
        "ssh",
        "-o",
        "BatchMode=yes",
        "-o",
        "ConnectTimeout=5",
        registration["ssh_target"],
        "python3",
        "-B",
        command["remote_helper_path"],
        "execute-allocation",
        "--command-manifest",
        str(command_manifest),
    ]
    try:
        process = subprocess.Popen(
            ssh_command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError as exc:
        raise ContractError("unable to start registered host allocation") from exc
    return AllocationProcess(
        allocation_id=allocation_row["allocation_id"],
        attempt_id=attempt_id,
        session_id=command["session_id"],
        process=process,
        run_dir=run_dir,
        launch=launch,
    )


def finish_allocation(handle: AllocationProcess, *, timeout: float = 120.0) -> dict[str, Any]:
    try:
        stdout, stderr = handle.process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        raise ContractError(
            f"allocation remains live and requires exact-unit cleanup: {handle.allocation_id}"
        ) from exc
    stdout_sha256 = sha256_bytes(stdout)
    stderr_sha256 = sha256_bytes(stderr)
    for stream, data, content_sha in (
        ("stdout", stdout, stdout_sha256),
        ("stderr", stderr, stderr_sha256),
    ):
        atomic_install_bytes(
            handle.run_dir / "multi-host-outputs" / stream,
            f"{content_sha}.bin",
            data,
            quarantine_root=handle.run_dir / "quarantine",
        )
    code = handle.process.returncode
    status = "completed" if code == 0 else ("lost" if code == 255 else "failed")
    terminal = _sealed(
        {
            "schema": TERMINAL_SCHEMA,
            "attempt_id": handle.attempt_id,
            "status": status,
            "exit_code": code,
            "stdout_sha256": stdout_sha256,
            "stdout_bytes": len(stdout),
            "stderr_sha256": stderr_sha256,
            "stderr_bytes": len(stderr),
            "ended_at_ns": time.time_ns(),
        }
    )
    atomic_install_json(
        handle.run_dir / "multi-host-terminals" / handle.allocation_id,
        f"{handle.attempt_id}.json",
        terminal,
        quarantine_root=handle.run_dir / "quarantine",
    )
    return terminal


def remote_liveness(
    *,
    registration: dict[str, Any],
    remote_helper_path: Path,
    unit: str,
    launcher_pid: int,
) -> dict[str, Any]:
    _require_e3_unit(unit)
    helper = _require_safe_absolute_path(remote_helper_path, "remote_helper_path")
    if type(launcher_pid) is not int or launcher_pid <= 0:
        raise ContractError("invalid remote launcher PID")
    command = [
        "ssh",
        "-o",
        "BatchMode=yes",
        "-o",
        "ConnectTimeout=5",
        registration["ssh_target"],
        "python3",
        "-B",
        str(helper),
        "liveness",
        "--unit",
        unit,
        "--launcher-pid",
        str(launcher_pid),
    ]
    completed = subprocess.run(
        command,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=20,
        check=False,
    )
    if completed.returncode != 0:
        raise ContractError("unable to establish failed allocation liveness")
    try:
        evidence = json.loads(completed.stdout)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError("remote liveness evidence is malformed") from exc
    if completed.stdout != canonical_bytes(evidence):
        raise ContractError("remote liveness evidence is non-canonical")
    expected = {"unit", "unit_state", "launcher_pid", "launcher_live"}
    if set(evidence) != expected or evidence["unit"] != unit:
        raise ContractError("remote liveness evidence field mismatch")
    return evidence


def kill_remote_launcher(
    *,
    registration: dict[str, Any],
    remote_helper_path: Path,
    unit: str,
    launcher_pid: int,
) -> dict[str, Any]:
    """Kill only the registered launcher after proving exact cgroup membership."""

    _require_e3_unit(unit)
    helper = _require_safe_absolute_path(remote_helper_path, "remote_helper_path")
    if type(launcher_pid) is not int or launcher_pid <= 0:
        raise ContractError("invalid remote launcher PID")
    completed = subprocess.run(
        [
            "ssh",
            "-o",
            "BatchMode=yes",
            "-o",
            "ConnectTimeout=5",
            registration["ssh_target"],
            "python3",
            "-B",
            str(helper),
            "kill-launcher",
            "--unit",
            unit,
            "--launcher-pid",
            str(launcher_pid),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=20,
        check=False,
    )
    if completed.returncode != 0:
        raise ContractError(
            "exact remote launcher kill failed: "
            + completed.stderr.decode("utf-8", errors="replace").strip()
        )
    try:
        evidence = json.loads(completed.stdout)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError("remote kill evidence is malformed") from exc
    if completed.stdout != canonical_bytes(evidence):
        raise ContractError("remote kill evidence is non-canonical")
    if (
        set(evidence)
        != {"unit", "launcher_pid", "cgroup_path", "signal", "killed_at_ns"}
        or evidence.get("unit") != unit
        or evidence.get("launcher_pid") != launcher_pid
        or evidence.get("signal") != signal.SIGKILL
    ):
        raise ContractError("remote kill evidence identity mismatch")
    return evidence


def remote_file_observation(
    *, registration: dict[str, Any], remote_helper_path: Path, path: Path
) -> dict[str, Any]:
    """Observe a shared marker through the owning host's NFS client."""

    helper = _require_safe_absolute_path(remote_helper_path, "remote_helper_path")
    observed_path = _require_safe_absolute_path(path, "observed_path")
    completed = subprocess.run(
        [
            "ssh",
            "-o",
            "BatchMode=yes",
            "-o",
            "ConnectTimeout=5",
            registration["ssh_target"],
            "python3",
            "-B",
            str(helper),
            "observe-file",
            "--path",
            str(observed_path),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=20,
        check=False,
    )
    if completed.returncode != 0:
        raise ContractError("remote file is not observable")
    try:
        evidence = json.loads(completed.stdout)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError("remote file observation is malformed") from exc
    if completed.stdout != canonical_bytes(evidence):
        raise ContractError("remote file observation is non-canonical")
    if (
        set(evidence) != {"path", "sha256", "bytes", "content_hex", "mtime_ns"}
        or evidence.get("path") != str(observed_path)
        or type(evidence.get("bytes")) is not int
        or evidence["bytes"] < 0
        or evidence["bytes"] > 4096
        or type(evidence.get("mtime_ns")) is not int
        or evidence["mtime_ns"] < 0
    ):
        raise ContractError("remote file observation field mismatch")
    _require_sha(evidence.get("sha256"), "remote file sha256")
    try:
        content = bytes.fromhex(evidence.get("content_hex", ""))
    except ValueError as exc:
        raise ContractError("remote file observation content is malformed") from exc
    if len(content) != evidence["bytes"] or sha256_bytes(content) != evidence["sha256"]:
        raise ContractError("remote file observation content mismatch")
    return evidence


def recover_failed_shard(
    *,
    plan: dict[str, Any],
    run: dict[str, Any],
    run_dir: Path,
    failed_allocation_id: str,
    retry_allocation_id: str,
    resource_session_id: str,
    remote_helper_path: Path,
    inspect_shared_root: bool = True,
) -> dict[str, Any]:
    validate_plan(plan, run, inspect_shared_root=inspect_shared_root)
    _require_safe(resource_session_id, "resource_session_id")
    allocations = {row["allocation_id"]: row for row in plan["allocations"]}
    failed = allocations.get(failed_allocation_id)
    retry = allocations.get(retry_allocation_id)
    if (
        failed is None
        or retry is None
        or retry["recovers_allocation_id"] != failed_allocation_id
        or len(retry["shard_ids"]) != 1
        or failed["shard_ids"] != retry["shard_ids"]
    ):
        raise ContractError("unregistered multi-host recovery")
    shard_id = retry["shard_ids"][0]
    recovery_path = (
        run_dir / "multi-host-recoveries" / f"{failed_allocation_id}-{shard_id}.json"
    )
    if recovery_path.exists():
        matches = [
            row
            for row in _load_recoveries(run_dir, plan, run)
            if row["failed_allocation_id"] == failed_allocation_id
            and row["retry_allocation_id"] == retry_allocation_id
            and row["resource_session_id"] == resource_session_id
            and row["shard_id"] == shard_id
        ]
        if len(matches) != 1:
            raise ContractError("host recovery replay mismatch")
        return matches[0]
    session_dir = run_dir / "resource-sessions" / resource_session_id
    preflight = read_canonical_json(session_dir / "preflight.json")
    if (session_dir / "terminal.json").exists():
        raise ContractError("resource session has a terminal and is not host-loss evidence")
    registrations = {row["host_id"]: row for row in plan["host_registrations"]}
    registration = registrations[failed["host_id"]]
    if (
        preflight.get("host_id") != registration["hostname"]
        or shard_id not in preflight.get("shard_ids", [])
    ):
        raise ContractError("resource session does not own the failed shard")
    unit = f"{run['resource_enforcement']['unit_prefix']}-{resource_session_id}.service"
    liveness = remote_liveness(
        registration=registration,
        remote_helper_path=remote_helper_path,
        unit=unit,
        launcher_pid=preflight["launcher_pid"],
    )
    if liveness["launcher_live"] or liveness["unit_state"] in {
        "active",
        "activating",
        "deactivating",
    }:
        raise ContractError("failed allocation is still live; lease recovery refused")
    lease_path = run_dir / "leases" / f"{shard_id}.json"
    lease = read_canonical_json(lease_path)
    recovery_id = f"{plan['plan_sha256'][:12]}-{failed_allocation_id}-{shard_id}"
    quarantine = recover_shard_lease(
        run_dir,
        str(shard_id),
        lease["owner_id"],
        recovery_id=recovery_id,
    )
    record = _sealed(
        {
            "schema": RECOVERY_SCHEMA,
            "plan_sha256": plan["plan_sha256"],
            "run_identity_sha256": run["identity_sha256"],
            "failed_allocation_id": failed_allocation_id,
            "retry_allocation_id": retry_allocation_id,
            "resource_session_id": resource_session_id,
            "shard_id": shard_id,
            "lease_owner_id": lease["owner_id"],
            "remote_unit": unit,
            "remote_unit_state": liveness["unit_state"],
            "launcher_pid": preflight["launcher_pid"],
            "launcher_live": liveness["launcher_live"],
            "observed_at_ns": time.time_ns(),
            "quarantine_path": str(quarantine.relative_to(run_dir)),
        }
    )
    atomic_install_json(
        recovery_path.parent,
        recovery_path.name,
        record,
        quarantine_root=run_dir / "quarantine",
    )
    return record


def recover_released_failed_shard(
    *,
    plan: dict[str, Any],
    run: dict[str, Any],
    run_dir: Path,
    failed_allocation_id: str,
    retry_allocation_id: str,
    resource_session_id: str,
    remote_helper_path: Path,
    inspect_shared_root: bool = True,
) -> dict[str, Any]:
    """Authorize one retry after a failed runner cleanly released its lease."""

    validate_plan(plan, run, inspect_shared_root=inspect_shared_root)
    _require_safe(resource_session_id, "resource_session_id")
    allocations = {row["allocation_id"]: row for row in plan["allocations"]}
    failed = allocations.get(failed_allocation_id)
    retry = allocations.get(retry_allocation_id)
    if (
        failed is None
        or retry is None
        or retry["recovers_allocation_id"] != failed_allocation_id
        or len(retry["shard_ids"]) != 1
    ):
        raise ContractError("unregistered multi-host recovery")
    shard_id = retry["shard_ids"][0]
    recovery_path = (
        run_dir / "multi-host-recoveries" / f"{failed_allocation_id}-{shard_id}.json"
    )
    session_dir = run_dir / "resource-sessions" / resource_session_id
    preflight, resource_terminal = validate_resource_session(
        run_dir=run_dir,
        run=run,
        session_id=resource_session_id,
        expected_status="failed",
    )
    registrations = {row["host_id"]: row for row in plan["host_registrations"]}
    registration = registrations[failed["host_id"]]
    if (
        preflight.get("host_id") != registration["hostname"]
        or shard_id not in preflight.get("shard_ids", [])
    ):
        raise ContractError("resource session does not own the failed shard")
    unit = f"{run['resource_enforcement']['unit_prefix']}-{resource_session_id}.service"
    liveness = remote_liveness(
        registration=registration,
        remote_helper_path=remote_helper_path,
        unit=unit,
        launcher_pid=preflight["launcher_pid"],
    )
    if liveness["launcher_live"] or liveness["unit_state"] in {
        "active",
        "activating",
        "deactivating",
    }:
        raise ContractError("failed allocation is still live; recovery refused")
    if (run_dir / "leases" / f"{shard_id}.json").exists():
        raise ContractError("released recovery found a live or stale shard lease")

    _commands, attempts, terminals = _load_allocation_evidence(
        run_dir, plan, inspect_shared_root=inspect_shared_root
    )
    failed_attempts = attempts.get(failed_allocation_id, [])
    if len(failed_attempts) != 1:
        raise ContractError("released recovery requires one failed allocation attempt")
    failed_attempt = failed_attempts[0]
    failed_terminal = terminals.get(failed_attempt["attempt_id"])
    if (
        failed_attempt.get("session_id") != resource_session_id
        or failed_terminal is None
        or failed_terminal.get("status") != "failed"
        or resource_terminal.get("worker_exit_codes")
        != [failed_terminal.get("exit_code")]
    ):
        raise ContractError("released recovery lacks its failed allocation terminal")

    runner_terminal_root = run_dir / "terminals" / str(shard_id)
    runner_terminal_paths = _json_files(runner_terminal_root)
    if len(runner_terminal_paths) != 1:
        raise ContractError("released recovery requires one runner terminal")
    runner_terminal_path = runner_terminal_paths[0]
    runner_terminal = read_canonical_json(runner_terminal_path)
    assignment = read_canonical_json(run_dir / "assignments" / f"{shard_id}.json")
    assigned_keys = assignment.get("result_keys")
    if (
        set(assignment) != {"shard_id", "result_keys"}
        or assignment.get("shard_id") != str(shard_id)
        or not isinstance(assigned_keys, list)
        or not assigned_keys
        or len(assigned_keys) != len(set(assigned_keys))
        or any(SHA256.fullmatch(key) is None for key in assigned_keys)
        or set(runner_terminal) != ATTEMPT_TERMINAL_FIELDS
        or runner_terminal.get("status") != "failed"
        or runner_terminal.get("exit_code") != 1
        or runner_terminal.get("signal") is not None
        or type(runner_terminal.get("wall_time_ns")) is not int
        or runner_terminal["wall_time_ns"] < 0
        or runner_terminal.get("peak_rss_bytes") != 0
        or runner_terminal.get("completed_count") != 0
        or runner_terminal.get("result_set_sha256") != record_set_sha256([])
        or runner_terminal.get("durable_result_keys") != []
        or runner_terminal.get("new_result_keys") != []
        or runner_terminal.get("skipped_result_keys") != []
        or runner_terminal.get("missing_result_keys") != sorted(assigned_keys)
        or type(runner_terminal.get("ended_at_ns")) is not int
        or runner_terminal["ended_at_ns"] < 0
    ):
        raise ContractError(
            "released recovery runner terminal is not exact zero-record failed"
        )
    if any(
        read_canonical_json(path).get("shard_id") == str(shard_id)
        for path in _json_files(run_dir / "records")
    ):
        raise ContractError("released recovery shard has durable result records")

    if recovery_path.exists():
        matches = [
            row
            for row in _load_recoveries(run_dir, plan, run)
            if row["failed_allocation_id"] == failed_allocation_id
            and row["retry_allocation_id"] == retry_allocation_id
            and row["resource_session_id"] == resource_session_id
            and row["shard_id"] == shard_id
            and row["schema"] == RELEASED_RECOVERY_SCHEMA
        ]
        if len(matches) != 1:
            raise ContractError("host recovery replay mismatch")
        return matches[0]

    record = _sealed(
        {
            "schema": RELEASED_RECOVERY_SCHEMA,
            "plan_sha256": plan["plan_sha256"],
            "run_identity_sha256": run["identity_sha256"],
            "failed_allocation_id": failed_allocation_id,
            "retry_allocation_id": retry_allocation_id,
            "resource_session_id": resource_session_id,
            "shard_id": shard_id,
            "failed_attempt_id": failed_attempt["attempt_id"],
            "failed_terminal_record_sha256": failed_terminal["record_sha256"],
            "runner_terminal_path": str(runner_terminal_path.relative_to(run_dir)),
            "runner_terminal_sha256": sha256_file(runner_terminal_path),
            "resource_terminal_record_sha256": resource_terminal["record_sha256"],
            "resource_terminal_sha256": sha256_file(session_dir / "terminal.json"),
            "lease_state": "released-after-failure",
            "remote_unit": unit,
            "remote_unit_state": liveness["unit_state"],
            "launcher_pid": preflight["launcher_pid"],
            "launcher_live": liveness["launcher_live"],
            "observed_at_ns": time.time_ns(),
        }
    )
    atomic_install_json(
        recovery_path.parent,
        recovery_path.name,
        record,
        quarantine_root=run_dir / "quarantine",
    )
    return record


def _json_files(directory: Path) -> list[Path]:
    if not directory.is_dir():
        raise ContractError(f"missing multi-host artifact directory: {directory}")
    invalid = [
        path.name
        for path in directory.iterdir()
        if path.is_symlink() or not path.is_file() or path.suffix != ".json"
    ]
    if invalid:
        raise ContractError(f"unexpected multi-host artifact: {sorted(invalid)[0]}")
    return sorted(directory.glob("*.json"), key=lambda path: path.name)


def _load_allocation_evidence(
    run_dir: Path, plan: dict[str, Any], *, inspect_shared_root: bool = True
) -> tuple[
    dict[str, dict[str, Any]],
    dict[str, list[dict[str, Any]]],
    dict[str, dict[str, Any]],
]:
    allocation_ids = {row["allocation_id"] for row in plan["allocations"]}
    commands: dict[str, dict[str, Any]] = {}
    for path in _json_files(run_dir / "multi-host-commands"):
        command = read_canonical_json(path)
        if path.name != f"{command.get('allocation_id')}.json":
            raise ContractError("host command filename/allocation mismatch")
        command_plan, command_run, _allocation = validate_host_command(
            command, inspect_shared_root=inspect_shared_root
        )
        if (
            command_plan["plan_sha256"] != plan["plan_sha256"]
            or command_run["identity_sha256"] != plan["run_identity_sha256"]
        ):
            raise ContractError("host command belongs to a different run or plan")
        allocation_id = command["allocation_id"]
        if allocation_id not in allocation_ids or allocation_id in commands:
            raise ContractError("unexpected or duplicate host command")
        commands[allocation_id] = command

    attempts_root = run_dir / "multi-host-attempts"
    terminals_root = run_dir / "multi-host-terminals"
    if not attempts_root.is_dir():
        raise ContractError("missing multi-host allocation attempts")
    attempts: dict[str, list[dict[str, Any]]] = {}
    terminals: dict[str, dict[str, Any]] = {}
    seen_attempt_ids: set[str] = set()
    for directory in sorted(attempts_root.iterdir(), key=lambda path: path.name):
        if not directory.is_dir() or directory.name not in allocation_ids:
            raise ContractError("unexpected allocation-attempt directory")
        rows = []
        for path in _json_files(directory):
            launch = read_canonical_json(path)
            if set(launch) != ATTEMPT_FIELDS or launch.get("schema") != ATTEMPT_SCHEMA:
                raise ContractError("allocation attempt field/schema mismatch")
            _validate_seal(launch)
            if (
                path.name != f"{launch.get('attempt_id')}.json"
                or launch.get("allocation_id") != directory.name
                or launch.get("plan_sha256") != plan["plan_sha256"]
                or launch.get("run_identity_sha256")
                != plan["run_identity_sha256"]
            ):
                raise ContractError("allocation attempt identity mismatch")
            for field in (
                "attempt_id",
                "allocation_id",
                "host_id",
                "session_id",
                "coordinator_host",
            ):
                _require_safe(launch.get(field), field)
            if (
                type(launch.get("coordinator_pid")) is not int
                or launch["coordinator_pid"] <= 0
                or type(launch.get("started_at_ns")) is not int
                or launch["started_at_ns"] < 0
            ):
                raise ContractError("invalid allocation attempt process identity")
            if launch["attempt_id"] in seen_attempt_ids:
                raise ContractError("duplicate allocation attempt identity")
            seen_attempt_ids.add(launch["attempt_id"])
            command = commands.get(directory.name)
            if command is None or launch["command_sha256"] != command["record_sha256"]:
                raise ContractError("allocation attempt command mismatch")
            if (
                launch["host_id"] != command["host_id"]
                or launch["session_id"] != command["session_id"]
            ):
                raise ContractError("allocation attempt ownership mismatch")
            rows.append(launch)
        attempts[directory.name] = rows
        if len(rows) != 1:
            raise ContractError("each host allocation must have exactly one attempt")

    if terminals_root.exists():
        for directory in sorted(terminals_root.iterdir(), key=lambda path: path.name):
            if not directory.is_dir() or directory.name not in attempts:
                raise ContractError("unexpected allocation-terminal directory")
            by_attempt = {row["attempt_id"]: row for row in attempts[directory.name]}
            for path in _json_files(directory):
                terminal = read_canonical_json(path)
                if set(terminal) != TERMINAL_FIELDS or terminal.get("schema") != TERMINAL_SCHEMA:
                    raise ContractError("allocation terminal field/schema mismatch")
                _validate_seal(terminal)
                attempt_id = terminal.get("attempt_id")
                launch = by_attempt.get(attempt_id)
                if launch is None or path.name != f"{attempt_id}.json":
                    raise ContractError("allocation terminal has no launch")
                code = terminal.get("exit_code")
                status = terminal.get("status")
                if (
                    type(code) is not int
                    or status not in {"completed", "failed", "lost"}
                    or (status == "completed") != (code == 0)
                    or (status == "lost") != (code == 255)
                    or type(terminal.get("ended_at_ns")) is not int
                    or terminal["ended_at_ns"] < launch["started_at_ns"]
                ):
                    raise ContractError("allocation terminal outcome mismatch")
                for stream in ("stdout", "stderr"):
                    content_sha = _require_sha(
                        terminal.get(f"{stream}_sha256"), f"{stream}_sha256"
                    )
                    byte_count = terminal.get(f"{stream}_bytes")
                    if type(byte_count) is not int or byte_count < 0:
                        raise ContractError("allocation terminal byte count mismatch")
                    sidecar = run_dir / "multi-host-outputs" / stream / f"{content_sha}.bin"
                    if (
                        not sidecar.is_file()
                        or sidecar.is_symlink()
                        or sidecar.stat().st_size != terminal[f"{stream}_bytes"]
                        or sha256_file(sidecar) != content_sha
                    ):
                        raise ContractError("allocation terminal output sidecar mismatch")
                if attempt_id in terminals:
                    raise ContractError("duplicate allocation terminal")
                terminals[attempt_id] = terminal
    return commands, attempts, terminals


def _post_run_quarantine_relative(
    diagnostic_relative: Path, diagnostic_sha256: str
) -> Path:
    if (
        diagnostic_relative.is_absolute()
        or len(diagnostic_relative.parts) != 3
        or diagnostic_relative.parts[0] != "terminals"
        or diagnostic_relative.suffix != ".json"
        or ".." in diagnostic_relative.parts
    ):
        raise ContractError("post-run diagnostic terminal path mismatch")
    _require_sha(diagnostic_sha256, "diagnostic terminal sha256")
    return (
        Path("quarantine")
        / "post-run-validation"
        / f"{diagnostic_sha256}-{diagnostic_relative.name}"
    )


def _raw_post_run_closures(run_dir: Path) -> list[dict[str, Any]]:
    root = run_dir / "quarantine" / "post-run-validation-closures"
    if not root.exists():
        return []
    rows = []
    for path in _json_files(root):
        record = read_canonical_json(path)
        if (
            set(record) != POST_RUN_CLOSURE_FIELDS
            or record.get("schema") != POST_RUN_CLOSURE_SCHEMA
        ):
            raise ContractError("post-run closure field/schema mismatch")
        _validate_seal(record)
        if path.name != f"{record.get('allocation_id')}.json":
            raise ContractError("post-run closure filename/allocation mismatch")
        rows.append(record)
    return rows


def _released_runner_terminal_path(
    run_dir: Path, record: dict[str, Any]
) -> Path:
    """Resolve released-failure evidence before or after exact quarantine."""

    source = run_dir / str(record.get("runner_terminal_path"))
    if source.is_file() and not source.is_symlink():
        return source
    matches = [
        closure
        for closure in _raw_post_run_closures(run_dir)
        if closure.get("diagnostic_terminal_path")
        == record.get("runner_terminal_path")
        and closure.get("diagnostic_terminal_sha256")
        == record.get("runner_terminal_sha256")
        and closure.get("recovery_record_sha256") == record.get("record_sha256")
    ]
    if len(matches) != 1:
        return source
    closure = matches[0]
    diagnostic_relative = Path(closure["diagnostic_terminal_path"])
    expected_quarantine = _post_run_quarantine_relative(
        diagnostic_relative, closure["diagnostic_terminal_sha256"]
    )
    if closure.get("quarantine_path") != str(expected_quarantine):
        raise ContractError("post-run closure quarantine identity mismatch")
    destination = run_dir / expected_quarantine
    if source.exists() or not destination.is_file() or destination.is_symlink():
        raise ContractError("post-run diagnostic terminal location mismatch")
    return destination


def _load_recoveries(
    run_dir: Path, plan: dict[str, Any], run: dict[str, Any]
) -> list[dict[str, Any]]:
    root = run_dir / "multi-host-recoveries"
    if not root.exists():
        return []
    allocations = {row["allocation_id"]: row for row in plan["allocations"]}
    recoveries = []
    for path in _json_files(root):
        record = read_canonical_json(path)
        schema = record.get("schema")
        expected_fields = (
            RECOVERY_FIELDS
            if schema == RECOVERY_SCHEMA
            else RELEASED_RECOVERY_FIELDS
            if schema == RELEASED_RECOVERY_SCHEMA
            else None
        )
        if expected_fields is None or set(record) != expected_fields:
            raise ContractError("host recovery field/schema mismatch")
        _validate_seal(record)
        expected_name = f"{record.get('failed_allocation_id')}-{record.get('shard_id')}.json"
        if path.name != expected_name:
            raise ContractError("host recovery filename/identity mismatch")
        failed = allocations.get(record.get("failed_allocation_id"))
        retry = allocations.get(record.get("retry_allocation_id"))
        if (
            failed is None
            or retry is None
            or retry["recovers_allocation_id"] != failed["allocation_id"]
            or retry["shard_ids"] != [record.get("shard_id")]
            or record.get("plan_sha256") != plan["plan_sha256"]
            or record.get("run_identity_sha256") != run["identity_sha256"]
            or record.get("launcher_live") is not False
            or record.get("remote_unit_state")
            in {"active", "activating", "deactivating"}
        ):
            raise ContractError("host recovery ownership/liveness mismatch")
        common_safe_fields = (
            "failed_allocation_id",
            "retry_allocation_id",
            "resource_session_id",
            "remote_unit",
        )
        for field in common_safe_fields:
            _require_safe(record.get(field), field)
        if (
            type(record.get("shard_id")) is not int
            or type(record.get("launcher_pid")) is not int
            or record["launcher_pid"] <= 0
            or type(record.get("observed_at_ns")) is not int
            or record["observed_at_ns"] < 0
        ):
            raise ContractError("invalid host recovery process identity")
        if schema == RECOVERY_SCHEMA:
            _require_safe(record.get("lease_owner_id"), "lease_owner_id")
            recovery_id = (
                f"{plan['plan_sha256'][:12]}-{failed['allocation_id']}-"
                f"{record['shard_id']}"
            )
            expected_quarantine = (
                Path("quarantine")
                / "stale-leases"
                / f"{record['shard_id']}.json.{recovery_id}"
            )
            if record.get("quarantine_path") != str(expected_quarantine):
                raise ContractError("host recovery quarantine identity mismatch")
            quarantine = run_dir / expected_quarantine
            if not quarantine.is_file() or quarantine.is_symlink():
                raise ContractError("host recovery quarantine evidence is missing")
            lease = read_canonical_json(quarantine)
            if lease.get("owner_id") != record.get("lease_owner_id"):
                raise ContractError("host recovery lease-owner mismatch")
        else:
            for field in ("failed_attempt_id",):
                _require_safe(record.get(field), field)
            _require_sha(
                record.get("failed_terminal_record_sha256"),
                "failed terminal record sha256",
            )
            _require_sha(
                record.get("runner_terminal_sha256"),
                "runner terminal sha256",
            )
            _require_sha(
                record.get("resource_terminal_record_sha256"),
                "resource terminal record sha256",
            )
            _require_sha(
                record.get("resource_terminal_sha256"),
                "resource terminal sha256",
            )
            if record.get("lease_state") != "released-after-failure":
                raise ContractError("released recovery lease state mismatch")
            if (run_dir / "leases" / f"{record['shard_id']}.json").exists():
                raise ContractError("released recovery shard lease reappeared")
            expected_runner_root = run_dir / "terminals" / str(record["shard_id"])
            runner_path = _released_runner_terminal_path(run_dir, record)
            expected_source = run_dir / str(record.get("runner_terminal_path"))
            allowed_parents = {
                expected_runner_root,
                run_dir / "quarantine" / "post-run-validation",
            }
            if (
                runner_path.parent not in allowed_parents
                or not runner_path.is_file()
                or runner_path.is_symlink()
                or sha256_file(runner_path) != record["runner_terminal_sha256"]
            ):
                raise ContractError("released recovery runner terminal mismatch")
            if (
                runner_path.parent == expected_runner_root
                and runner_path != expected_source
            ):
                raise ContractError("released recovery runner terminal mismatch")
            runner_terminal = read_canonical_json(runner_path)
            if (
                runner_terminal.get("status") != "failed"
                or runner_terminal.get("completed_count") != 0
                or runner_terminal.get("durable_result_keys") != []
                or runner_terminal.get("new_result_keys") != []
                or runner_terminal.get("skipped_result_keys") != []
            ):
                raise ContractError("released recovery runner outcome mismatch")
            allocation_attempt_root = (
                run_dir / "multi-host-attempts" / failed["allocation_id"]
            )
            allocation_terminal_root = (
                run_dir / "multi-host-terminals" / failed["allocation_id"]
            )
            attempt_path = (
                allocation_attempt_root / f"{record['failed_attempt_id']}.json"
            )
            terminal_path = (
                allocation_terminal_root / f"{record['failed_attempt_id']}.json"
            )
            if not attempt_path.is_file() or not terminal_path.is_file():
                raise ContractError("released recovery allocation evidence is missing")
            failed_attempt = read_canonical_json(attempt_path)
            failed_terminal = read_canonical_json(terminal_path)
            resource_preflight, resource_terminal = validate_resource_session(
                run_dir=run_dir,
                run=run,
                session_id=record["resource_session_id"],
                expected_status="failed",
            )
            resource_terminal_path = (
                run_dir
                / "resource-sessions"
                / record["resource_session_id"]
                / "terminal.json"
            )
            if (
                failed_attempt.get("attempt_id") != record["failed_attempt_id"]
                or failed_attempt.get("allocation_id") != failed["allocation_id"]
                or failed_attempt.get("session_id") != record["resource_session_id"]
                or failed_terminal.get("status") != "failed"
                or failed_terminal.get("record_sha256")
                != record["failed_terminal_record_sha256"]
                or resource_terminal.get("worker_exit_codes")
                != [failed_terminal.get("exit_code")]
                or resource_terminal.get("record_sha256")
                != record["resource_terminal_record_sha256"]
                or sha256_file(resource_terminal_path)
                != record["resource_terminal_sha256"]
            ):
                raise ContractError("released recovery failed terminal mismatch")
        session = (
            resource_preflight
            if schema == RELEASED_RECOVERY_SCHEMA
            else read_canonical_json(
                run_dir
                / "resource-sessions"
                / record["resource_session_id"]
                / "preflight.json"
            )
        )
        if (
            session.get("launcher_pid") != record.get("launcher_pid")
            or session.get("run_identity_sha256") != run["identity_sha256"]
            or session.get("shard_ids") is None
            or record["shard_id"] not in session["shard_ids"]
            or record["observed_at_ns"] < session.get("started_at_ns", 0)
        ):
            raise ContractError("host recovery launcher mismatch")
        recoveries.append(record)
    return recoveries


def _post_run_locations(
    run_dir: Path, closure: dict[str, Any]
) -> tuple[Path, Path, Path]:
    diagnostic_relative = Path(str(closure.get("diagnostic_terminal_path")))
    diagnostic_sha256 = str(closure.get("diagnostic_terminal_sha256"))
    expected_quarantine = _post_run_quarantine_relative(
        diagnostic_relative, diagnostic_sha256
    )
    if closure.get("quarantine_path") != str(expected_quarantine):
        raise ContractError("post-run closure quarantine identity mismatch")
    source = run_dir / diagnostic_relative
    destination = run_dir / expected_quarantine
    present = [path for path in (source, destination) if path.is_file()]
    if len(present) != 1 or any(path.is_symlink() for path in present):
        raise ContractError("post-run diagnostic terminal location mismatch")
    if sha256_file(present[0]) != diagnostic_sha256:
        raise ContractError("post-run diagnostic terminal hash mismatch")
    return source, destination, present[0]


def _post_run_bundle(
    run_dir: Path, closure: dict[str, Any]
) -> tuple[Any, Path, Path]:
    source, destination, present = _post_run_locations(run_dir, closure)
    if present != destination:
        raise ContractError("post-run diagnostic terminal is not quarantined")
    return load_bundle(run_dir), source, destination


def _require_file_sha(path: Path, expected: Any, label: str) -> None:
    _require_sha(expected, label)
    if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
        raise ContractError(f"post-run closure {label} mismatch")


def _load_post_run_closures(
    run_dir: Path,
    plan: dict[str, Any],
    run: dict[str, Any],
    commands: dict[str, dict[str, Any]],
    attempts: dict[str, list[dict[str, Any]]],
    terminals: dict[str, dict[str, Any]],
    recoveries: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], Any | None]:
    records = _raw_post_run_closures(run_dir)
    if not records:
        return [], None
    if len(records) != 1:
        raise ContractError("multiple post-run closures are unsupported")
    closure = records[0]
    if (
        closure.get("plan_sha256") != plan["plan_sha256"]
        or closure.get("run_identity_sha256") != run["identity_sha256"]
        or closure.get("error_class") != "terminal-without-launch-manifest"
        or closure.get("launcher_live") is not False
        or closure.get("remote_unit_state")
        in {"active", "activating", "deactivating"}
    ):
        raise ContractError("post-run closure identity/liveness mismatch")
    for field in (
        "allocation_id",
        "allocation_attempt_id",
        "resource_session_id",
        "runner_attempt_id",
        "remote_unit",
    ):
        _require_safe(closure.get(field), field)
    for field in ("shard_id", "launcher_pid", "observed_at_ns"):
        if type(closure.get(field)) is not int or closure[field] < 0:
            raise ContractError(f"invalid post-run closure field: {field}")
    _require_e3_unit(closure["remote_unit"])
    if closure["launcher_pid"] <= 0:
        raise ContractError("invalid post-run closure launcher PID")

    allocation_id = closure["allocation_id"]
    allocation_rows = attempts.get(allocation_id, [])
    if len(allocation_rows) != 1:
        raise ContractError("post-run closure lacks its allocation attempt")
    allocation_attempt = allocation_rows[0]
    allocation_terminal = terminals.get(allocation_attempt["attempt_id"])
    command = commands.get(allocation_id)
    recovery_matches = [
        row
        for row in recoveries
        if row["retry_allocation_id"] == allocation_id
        and row["shard_id"] == closure["shard_id"]
        and row["record_sha256"] == closure["recovery_record_sha256"]
    ]
    if (
        command is None
        or len(recovery_matches) != 1
        or allocation_attempt["attempt_id"] != closure["allocation_attempt_id"]
        or allocation_attempt["session_id"] != closure["resource_session_id"]
        or allocation_attempt["record_sha256"]
        != closure["allocation_attempt_record_sha256"]
        or allocation_terminal is None
        or allocation_terminal.get("status") != "failed"
        or allocation_terminal.get("exit_code") != 2
        or allocation_terminal.get("record_sha256")
        != closure["allocation_terminal_record_sha256"]
        or allocation_terminal.get("stderr_sha256") != closure["stderr_sha256"]
    ):
        raise ContractError("post-run closure allocation outcome mismatch")

    allocation_attempt_path = (
        run_dir
        / "multi-host-attempts"
        / allocation_id
        / f"{allocation_attempt['attempt_id']}.json"
    )
    allocation_terminal_path = (
        run_dir
        / "multi-host-terminals"
        / allocation_id
        / f"{allocation_attempt['attempt_id']}.json"
    )
    _require_file_sha(
        allocation_attempt_path,
        closure["allocation_attempt_sha256"],
        "allocation attempt sha256",
    )
    _require_file_sha(
        allocation_terminal_path,
        closure["allocation_terminal_sha256"],
        "allocation terminal sha256",
    )
    stderr_path = (
        run_dir
        / "multi-host-outputs"
        / "stderr"
        / f"{closure['stderr_sha256']}.bin"
    )
    _require_file_sha(stderr_path, closure["stderr_sha256"], "stderr sha256")
    stderr_bytes = stderr_path.read_bytes()
    error_prefix = b"terminal has no launch manifest: "
    diagnostic_suffix = (
        b"/" + closure["diagnostic_terminal_path"].encode("utf-8") + b"\n"
    )
    if error_prefix not in stderr_bytes or diagnostic_suffix not in stderr_bytes:
        raise ContractError("post-run closure stderr error-class mismatch")

    preflight, resource_terminal = validate_resource_session(
        run_dir=run_dir,
        run=run,
        session_id=closure["resource_session_id"],
        expected_status="failed",
    )
    preflight_path = (
        run_dir
        / "resource-sessions"
        / closure["resource_session_id"]
        / "preflight.json"
    )
    resource_terminal_path = preflight_path.with_name("terminal.json")
    if (
        preflight.get("record_sha256")
        != closure["resource_preflight_record_sha256"]
        or resource_terminal.get("record_sha256")
        != closure["resource_terminal_record_sha256"]
        or resource_terminal.get("worker_exit_codes") != [2]
        or preflight.get("launcher_pid") != closure["launcher_pid"]
        or preflight.get("shard_ids") != [closure["shard_id"]]
    ):
        raise ContractError("post-run closure resource outcome mismatch")
    _require_file_sha(
        preflight_path,
        closure["resource_preflight_sha256"],
        "resource preflight sha256",
    )
    _require_file_sha(
        resource_terminal_path,
        closure["resource_terminal_sha256"],
        "resource terminal sha256",
    )

    bundle, source, destination = _post_run_bundle(run_dir, closure)
    shard_id = str(closure["shard_id"])
    runner_attempts = bundle.attempts.get(shard_id, [])
    if len(runner_attempts) != 1:
        raise ContractError("post-run closure runner attempt mismatch")
    runner_attempt = runner_attempts[0]
    runner_terminal = runner_attempt.get("terminal")
    shard_completion = bundle.completions.get(shard_id)
    if (
        runner_attempt.get("attempt_id") != closure["runner_attempt_id"]
        or runner_attempt.get("resource_session_id")
        != closure["resource_session_id"]
        or runner_terminal is None
        or runner_terminal.get("status") != "completed"
        or runner_terminal.get("exit_code") != 0
        or runner_terminal.get("missing_result_keys") != []
        or shard_completion is None
        or shard_completion.get("state") != "complete"
        or shard_completion.get("attempt_ids") != [closure["runner_attempt_id"]]
        or shard_completion.get("unclosed_attempt_ids") != []
    ):
        raise ContractError("post-run closure inner runner outcome mismatch")
    runner_attempt_path = (
        run_dir / "attempts" / shard_id / f"{closure['runner_attempt_id']}.json"
    )
    runner_terminal_path = (
        run_dir / "terminals" / shard_id / f"{closure['runner_attempt_id']}.json"
    )
    completion_path = run_dir / "completions" / f"{shard_id}.json"
    _require_file_sha(
        runner_attempt_path,
        closure["runner_attempt_sha256"],
        "runner attempt sha256",
    )
    _require_file_sha(
        runner_terminal_path,
        closure["runner_terminal_sha256"],
        "runner terminal sha256",
    )
    _require_file_sha(
        completion_path,
        closure["shard_completion_sha256"],
        "shard completion sha256",
    )
    diagnostic_id = Path(closure["diagnostic_terminal_path"]).stem
    if any(
        attempt.get("attempt_id") == diagnostic_id
        for shard_attempts in bundle.attempts.values()
        for attempt in shard_attempts
    ):
        raise ContractError("post-run diagnostic unexpectedly has a launch")
    if (run_dir / "leases" / f"{shard_id}.json").exists():
        raise ContractError("post-run closure shard lease reappeared")
    if record_set_sha256(bundle.records) != closure["record_set_sha256"]:
        raise ContractError("post-run closure record set mismatch")
    canonical = sha256_bytes(merge_complete(bundle))
    if canonical != closure["canonical_bundle_sha256"]:
        raise ContractError("post-run closure canonical bundle mismatch")
    latest = max(
        allocation_terminal["ended_at_ns"],
        resource_terminal["ended_at_ns"],
        runner_terminal["ended_at_ns"],
    )
    if closure["observed_at_ns"] < latest:
        raise ContractError("post-run closure predates terminal evidence")
    if source.exists() == destination.exists():
        raise ContractError("post-run diagnostic terminal replay mismatch")
    return records, bundle


def _migrate_post_run_diagnostic(
    run_dir: Path,
    closure: dict[str, Any],
    *,
    phase_hook: Callable[[str], None] | None = None,
) -> None:
    source, destination, _present = _post_run_locations(run_dir, closure)
    if destination.exists():
        return
    destination.parent.mkdir(parents=True, exist_ok=True)
    os.replace(source, destination)
    for directory in (source.parent, destination.parent, destination.parent.parent):
        descriptor = os.open(directory, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    if phase_hook is not None:
        phase_hook("after_post_run_quarantine")


def close_post_run_validation_failure(
    *,
    plan: dict[str, Any],
    run: dict[str, Any],
    run_dir: Path,
    allocation_id: str,
    shard_id: int,
    remote_helper_path: Path,
    expected_record_set_sha256: str,
    expected_canonical_bundle_sha256: str,
    inspect_shared_root: bool = True,
    phase_hook: Callable[[str], None] | None = None,
) -> dict[str, Any]:
    """Close one exact post-run finalizer failure without launching work."""

    validate_plan(plan, run, inspect_shared_root=inspect_shared_root)
    closure_root = run_dir / "quarantine" / "post-run-validation-closures"
    closure_path = closure_root / f"{_require_safe(allocation_id, 'allocation_id')}.json"
    existing = _raw_post_run_closures(run_dir)
    if existing:
        if len(existing) != 1 or existing[0].get("allocation_id") != allocation_id:
            raise ContractError("post-run closure replay mismatch")
        _migrate_post_run_diagnostic(run_dir, existing[0], phase_hook=phase_hook)
        commands, attempts, terminals = _load_allocation_evidence(
            run_dir, plan, inspect_shared_root=inspect_shared_root
        )
        recoveries = _load_recoveries(run_dir, plan, run)
        validated, _bundle = _load_post_run_closures(
            run_dir, plan, run, commands, attempts, terminals, recoveries
        )
        return validated[0]

    commands, attempts, terminals = _load_allocation_evidence(
        run_dir, plan, inspect_shared_root=inspect_shared_root
    )
    recoveries = _load_recoveries(run_dir, plan, run)
    recovery_matches = [
        row
        for row in recoveries
        if row["retry_allocation_id"] == allocation_id and row["shard_id"] == shard_id
    ]
    allocation_rows = attempts.get(allocation_id, [])
    if len(recovery_matches) != 1 or len(allocation_rows) != 1:
        raise ContractError("post-run closure lacks exact recovery/allocation")
    recovery = recovery_matches[0]
    allocation_attempt = allocation_rows[0]
    allocation_terminal = terminals.get(allocation_attempt["attempt_id"])
    if allocation_terminal is None:
        raise ContractError("post-run closure allocation remains unclosed")
    diagnostic_relative = Path(recovery["runner_terminal_path"])
    diagnostic_sha256 = recovery["runner_terminal_sha256"]
    quarantine_relative = _post_run_quarantine_relative(
        diagnostic_relative, diagnostic_sha256
    )
    source = run_dir / diagnostic_relative
    if (
        not source.is_file()
        or source.is_symlink()
        or sha256_file(source) != diagnostic_sha256
        or (run_dir / quarantine_relative).exists()
    ):
        raise ContractError("post-run closure diagnostic source mismatch")
    records = [
        read_canonical_json(path) for path in _json_files(run_dir / "records")
    ]
    if record_set_sha256(records) != expected_record_set_sha256:
        raise ContractError("post-run closure expected record set mismatch")
    runner_attempt_paths = _json_files(run_dir / "attempts" / str(shard_id))
    if len(runner_attempt_paths) != 1:
        raise ContractError("post-run closure inner runner is incomplete")
    runner_attempt = read_canonical_json(runner_attempt_paths[0])
    runner_terminal_path = (
        run_dir
        / "terminals"
        / str(shard_id)
        / f"{runner_attempt.get('attempt_id')}.json"
    )
    completion_path = run_dir / "completions" / f"{shard_id}.json"
    if not runner_terminal_path.is_file() or not completion_path.is_file():
        raise ContractError("post-run closure inner runner is incomplete")
    runner_terminal = read_canonical_json(runner_terminal_path)
    shard_completion = read_canonical_json(completion_path)
    if (
        allocation_terminal.get("status") != "failed"
        or allocation_terminal.get("exit_code") != 2
        or runner_terminal.get("status") != "completed"
        or shard_completion.get("state") != "complete"
    ):
        raise ContractError("post-run closure outcome class mismatch")
    session_id = allocation_attempt["session_id"]
    preflight, resource_terminal = validate_resource_session(
        run_dir=run_dir,
        run=run,
        session_id=session_id,
        expected_status="failed",
    )
    if resource_terminal.get("worker_exit_codes") != [2]:
        raise ContractError("post-run closure resource exit mismatch")
    allocation = next(
        (row for row in plan["allocations"] if row["allocation_id"] == allocation_id),
        None,
    )
    if allocation is None or allocation.get("shard_ids") != [shard_id]:
        raise ContractError("post-run closure allocation mapping mismatch")
    registration = next(
        row
        for row in plan["host_registrations"]
        if row["host_id"] == allocation["host_id"]
    )
    unit = f"{run['resource_enforcement']['unit_prefix']}-{session_id}.service"
    liveness = remote_liveness(
        registration=registration,
        remote_helper_path=remote_helper_path,
        unit=unit,
        launcher_pid=preflight["launcher_pid"],
    )
    if (
        liveness.get("unit") != unit
        or liveness.get("launcher_pid") != preflight["launcher_pid"]
        or liveness.get("launcher_live") is not False
        or liveness.get("unit_state") in {"active", "activating", "deactivating"}
        or (run_dir / "leases" / f"{shard_id}.json").exists()
    ):
        raise ContractError("post-run closure process or lease is still live")

    allocation_attempt_path = (
        run_dir
        / "multi-host-attempts"
        / allocation_id
        / f"{allocation_attempt['attempt_id']}.json"
    )
    allocation_terminal_path = (
        run_dir
        / "multi-host-terminals"
        / allocation_id
        / f"{allocation_attempt['attempt_id']}.json"
    )
    preflight_path = run_dir / "resource-sessions" / session_id / "preflight.json"
    resource_terminal_path = preflight_path.with_name("terminal.json")
    runner_attempt_path = runner_attempt_paths[0]
    shard_completion_path = completion_path
    record = _sealed(
        {
            "schema": POST_RUN_CLOSURE_SCHEMA,
            "plan_sha256": plan["plan_sha256"],
            "run_identity_sha256": run["identity_sha256"],
            "recovery_record_sha256": recovery["record_sha256"],
            "allocation_id": allocation_id,
            "allocation_attempt_id": allocation_attempt["attempt_id"],
            "allocation_attempt_sha256": sha256_file(allocation_attempt_path),
            "allocation_attempt_record_sha256": allocation_attempt["record_sha256"],
            "allocation_terminal_sha256": sha256_file(allocation_terminal_path),
            "allocation_terminal_record_sha256": allocation_terminal["record_sha256"],
            "resource_session_id": session_id,
            "resource_preflight_sha256": sha256_file(preflight_path),
            "resource_preflight_record_sha256": preflight["record_sha256"],
            "resource_terminal_sha256": sha256_file(resource_terminal_path),
            "resource_terminal_record_sha256": resource_terminal["record_sha256"],
            "shard_id": shard_id,
            "runner_attempt_id": runner_attempt["attempt_id"],
            "runner_attempt_sha256": sha256_file(runner_attempt_path),
            "runner_terminal_sha256": sha256_file(runner_terminal_path),
            "shard_completion_sha256": sha256_file(shard_completion_path),
            "diagnostic_terminal_path": str(diagnostic_relative),
            "diagnostic_terminal_sha256": diagnostic_sha256,
            "quarantine_path": str(quarantine_relative),
            "stderr_sha256": allocation_terminal["stderr_sha256"],
            "error_class": "terminal-without-launch-manifest",
            "record_set_sha256": expected_record_set_sha256,
            "canonical_bundle_sha256": expected_canonical_bundle_sha256,
            "remote_unit": unit,
            "remote_unit_state": liveness["unit_state"],
            "launcher_pid": preflight["launcher_pid"],
            "launcher_live": False,
            "observed_at_ns": time.time_ns(),
        }
    )
    atomic_install_json(
        closure_path.parent,
        closure_path.name,
        record,
        quarantine_root=run_dir / "quarantine",
    )
    if phase_hook is not None:
        phase_hook("after_post_run_closure")
    _migrate_post_run_diagnostic(run_dir, record, phase_hook=phase_hook)
    commands, attempts, terminals = _load_allocation_evidence(
        run_dir, plan, inspect_shared_root=inspect_shared_root
    )
    recoveries = _load_recoveries(run_dir, plan, run)
    validated, _bundle = _load_post_run_closures(
        run_dir, plan, run, commands, attempts, terminals, recoveries
    )
    return validated[0]


def _load_fault_observation(
    run_dir: Path,
    plan: dict[str, Any],
    run: dict[str, Any],
    commands: dict[str, dict[str, Any]],
    attempts: dict[str, list[dict[str, Any]]],
    terminals: dict[str, dict[str, Any]],
) -> dict[str, Any] | None:
    path = run_dir / "multi-host-fault.json"
    fault = plan["fault_injection"]
    if fault["kind"] == "none":
        if path.exists():
            raise ContractError("non-fault plan contains a fault observation")
        return None
    if not path.is_file() or path.is_symlink():
        raise ContractError("fault-injection plan lacks its exact observation")
    record = read_canonical_json(path)
    if set(record) != FAULT_FIELDS or record.get("schema") != FAULT_SCHEMA:
        raise ContractError("fault observation field/schema mismatch")
    _validate_seal(record)
    allocation_id = fault["allocation_id"]
    command = commands.get(allocation_id)
    rows = attempts.get(allocation_id, [])
    if command is None or len(rows) != 1:
        raise ContractError("fault observation lacks its allocation attempt")
    launch = rows[0]
    preflight = read_canonical_json(
        run_dir / "resource-sessions" / command["session_id"] / "preflight.json"
    )
    expected_unit = (
        f"{run['resource_enforcement']['unit_prefix']}-{command['session_id']}.service"
    )
    content_hex = record.get("marker_content_hex")
    try:
        marker_content = bytes.fromhex(content_hex)
    except (TypeError, ValueError) as exc:
        raise ContractError("fault marker content is malformed") from exc
    terminal = terminals.get(launch["attempt_id"])
    if (
        record.get("plan_sha256") != plan["plan_sha256"]
        or record.get("run_identity_sha256") != run["identity_sha256"]
        or record.get("allocation_id") != allocation_id
        or record.get("resource_session_id") != command["session_id"]
        or record.get("marker_path") != fault["marker_path"]
        or record.get("remote_unit") != expected_unit
        or record.get("launcher_pid") != preflight.get("launcher_pid")
        or Path(str(record.get("cgroup_path", ""))).name != expected_unit
        or record.get("signal") != signal.SIGKILL
        or terminal is not None
        and terminal.get("status") == "completed"
    ):
        raise ContractError("fault observation ownership mismatch")
    _require_sha(record.get("marker_sha256"), "fault marker sha256")
    for field in ("marker_bytes", "marker_mtime_ns", "launcher_pid", "killed_at_ns"):
        if type(record.get(field)) is not int or record[field] < 0:
            raise ContractError(f"invalid fault observation field: {field}")
    if (
        record["marker_bytes"] > 4096
        or len(marker_content) != record["marker_bytes"]
        or sha256_bytes(marker_content) != record["marker_sha256"]
        or record["killed_at_ns"] < launch["started_at_ns"]
    ):
        raise ContractError("fault marker/kill observation mismatch")
    return record


def validate_multi_host_state(
    run_dir: Path,
    bundle: Any,
    *,
    require_completion: bool,
    inspect_shared_root: bool = True,
) -> dict[str, Any]:
    run = bundle.run
    if run["resource_enforcement"]["kind"] != MULTI_HOST_KIND:
        raise ContractError("multi-host evidence attached to a non-E3 run")
    plan = read_canonical_json(run_dir / "multi-host-plan.json")
    validate_plan(plan, run, inspect_shared_root=inspect_shared_root)
    commands, attempts, terminals = _load_allocation_evidence(
        run_dir, plan, inspect_shared_root=inspect_shared_root
    )
    recoveries = _load_recoveries(run_dir, plan, run)
    post_run_closures, post_run_bundle = _load_post_run_closures(
        run_dir, plan, run, commands, attempts, terminals, recoveries
    )
    if post_run_bundle is not None:
        bundle = post_run_bundle
    fault_observation = _load_fault_observation(
        run_dir, plan, run, commands, attempts, terminals
    )
    allocations = {row["allocation_id"]: row for row in plan["allocations"]}
    initial_ids = {
        allocation_id
        for allocation_id, row in allocations.items()
        if row["generation"] == 0
    }
    if (
        not initial_ids <= set(commands)
        or not initial_ids <= set(attempts)
        or any(not attempts[allocation_id] for allocation_id in initial_ids)
    ):
        raise ContractError("not every initial allocation was attempted")
    recovered_retry_ids = {row["retry_allocation_id"] for row in recoveries}
    if (
        not recovered_retry_ids <= set(commands)
        or not recovered_retry_ids <= set(attempts)
        or any(not attempts[allocation_id] for allocation_id in recovered_retry_ids)
    ):
        raise ContractError("host recovery lacks its retry allocation attempt")
    attempted_retry_ids = set(attempts) - initial_ids
    if attempted_retry_ids != recovered_retry_ids:
        raise ContractError("retry allocation lacks exact recovery authority")
    session_ids = [command["session_id"] for command in commands.values()]
    if len(session_ids) != len(set(session_ids)):
        raise ContractError("host commands reuse a resource session")
    resource_sessions = {
        path.name
        for path in (run_dir / "resource-sessions").iterdir()
        if path.is_dir()
    }
    if resource_sessions != {
        launch["session_id"] for rows in attempts.values() for launch in rows
    }:
        raise ContractError("resource session lacks exact allocation attribution")
    for allocation_id, rows in attempts.items():
        allocation_row = allocations[allocation_id]
        registration = next(
            row
            for row in plan["host_registrations"]
            if row["host_id"] == allocation_row["host_id"]
        )
        for launch in rows:
            if launch["session_id"] not in resource_sessions:
                raise ContractError("allocation attempt lacks its resource session")
            preflight = read_canonical_json(
                run_dir
                / "resource-sessions"
                / launch["session_id"]
                / "preflight.json"
            )
            if (
                preflight.get("host_id") != registration["hostname"]
                or preflight.get("shard_ids") != allocation_row["shard_ids"]
            ):
                raise ContractError("allocation/resource-session ownership mismatch")
            terminal = terminals.get(launch["attempt_id"])
            session_terminal = (
                run_dir / "resource-sessions" / launch["session_id"] / "terminal.json"
            )
            if terminal is not None and terminal["status"] == "completed":
                if not session_terminal.is_file():
                    raise ContractError("completed allocation lacks resource terminal")
                resource_terminal = read_canonical_json(session_terminal)
                if resource_terminal.get("status") != "completed":
                    raise ContractError("allocation/resource terminal outcome mismatch")
    all_launches = [row for rows in attempts.values() for row in rows]
    launch_ids = sorted(row["attempt_id"] for row in all_launches)
    unclosed_ids = sorted(set(launch_ids) - set(terminals))
    recovery_hashes = sorted(row["record_sha256"] for row in recoveries)
    recovery_by_failed_shard: dict[tuple[str, int], dict[str, Any]] = {}
    for row in recoveries:
        key = (row["failed_allocation_id"], row["shard_id"])
        if key in recovery_by_failed_shard:
            raise ContractError("duplicate host recovery authority")
        recovery_by_failed_shard[key] = row

    post_run_completed_allocations = {
        row["allocation_id"] for row in post_run_closures
    }

    def allocation_completed(allocation_id: str) -> bool:
        return any(
            terminals.get(row["attempt_id"], {}).get("status") == "completed"
            for row in attempts[allocation_id]
        ) or allocation_id in post_run_completed_allocations

    for allocation_id in initial_ids:
        allocation_row = allocations[allocation_id]
        allocation_attempts = attempts[allocation_id]
        if allocation_completed(allocation_id):
            if any(
                row["failed_allocation_id"] == allocation_id for row in recoveries
            ):
                raise ContractError("completed initial allocation has recovery evidence")
            continue
        for shard_id in allocation_row["shard_ids"]:
            recovery = recovery_by_failed_shard.get((allocation_id, shard_id))
            if recovery is None:
                raise ContractError("failed initial allocation lacks exact recovery")
            retry_id = recovery["retry_allocation_id"]
            if not allocation_completed(retry_id):
                raise ContractError("retry allocation did not complete")
            if not any(
                row["session_id"] == recovery["resource_session_id"]
                for row in allocation_attempts
            ):
                raise ContractError("host recovery names an unrelated allocation session")
    computed = {
        "plan_sha256": plan["plan_sha256"],
        "run_identity_sha256": run["identity_sha256"],
        "allocation_attempt_ids": launch_ids,
        "unclosed_allocation_attempt_ids": unclosed_ids,
        "recovery_record_sha256s": recovery_hashes,
        "resource_session_ids": sorted(resource_sessions),
        "canonical_bundle_sha256": sha256_bytes(merge_complete(bundle)),
    }
    if post_run_closures:
        computed["post_run_closure_record_sha256s"] = sorted(
            row["record_sha256"] for row in post_run_closures
        )
    resource_completion = read_canonical_json(run_dir / "resource-completion.json")
    recovered_session_ids = sorted(
        {
            row["resource_session_id"]
            for row in recoveries
            if not (
                run_dir
                / "resource-sessions"
                / row["resource_session_id"]
                / "terminal.json"
            ).is_file()
        }
    )
    if resource_completion.get("unclosed_session_ids") != recovered_session_ids:
        raise ContractError("resource completion has unaccounted unclosed sessions")
    computed["resource_completion_sha256"] = resource_completion["record_sha256"]
    computed["fault_record_sha256"] = (
        fault_observation["record_sha256"]
        if fault_observation is not None
        else None
    )
    if require_completion:
        completion = read_canonical_json(run_dir / "multi-host-completion.json")
        expected_fields = (
            POST_RUN_COMPLETION_FIELDS if post_run_closures else COMPLETION_FIELDS
        )
        expected_schema = (
            POST_RUN_COMPLETION_SCHEMA if post_run_closures else COMPLETION_SCHEMA
        )
        if set(completion) != expected_fields or completion.get("schema") != expected_schema:
            raise ContractError("multi-host completion field/schema mismatch")
        _validate_seal(completion)
        for field, value in computed.items():
            if completion.get(field) != value:
                raise ContractError(f"multi-host completion mismatch: {field}")
        if (
            type(completion.get("completed_at_ns")) is not int
            or completion["completed_at_ns"]
            < max(
                [resource_completion.get("completed_at_ns", 0)]
                + [row["started_at_ns"] for row in all_launches]
                + [row["ended_at_ns"] for row in terminals.values()]
                + [row["observed_at_ns"] for row in recoveries]
                + [row["observed_at_ns"] for row in post_run_closures]
                + (
                    [fault_observation["killed_at_ns"]]
                    if fault_observation is not None
                    else []
                )
            )
        ):
            raise ContractError("invalid multi-host completion timestamp")
        return completion
    return computed


def build_multi_host_completion(
    run_dir: Path, *, inspect_shared_root: bool = True
) -> dict[str, Any]:
    bundle = load_bundle(run_dir)
    verify_output_sidecars(run_dir, bundle.records)
    validate_resource_evidence(run_dir, bundle)
    computed = validate_multi_host_state(
        run_dir,
        bundle,
        require_completion=False,
        inspect_shared_root=inspect_shared_root,
    )
    return _sealed(
        {
            "schema": (
                POST_RUN_COMPLETION_SCHEMA
                if "post_run_closure_record_sha256s" in computed
                else COMPLETION_SCHEMA
            ),
            **computed,
            "completed_at_ns": time.time_ns(),
        }
    )


def finalize_multi_host_run(run_dir: Path) -> dict[str, Any]:
    bundle = load_bundle(run_dir)
    if (run_dir / "multi-host-completion.json").exists():
        completion = validate_multi_host_state(
            run_dir, bundle, require_completion=True
        )
        validate_resource_evidence(run_dir, bundle)
        return completion
    if not (run_dir / "resource-completion.json").exists():
        install_resource_completion(
            run_dir,
            build_resource_completion(run=bundle.run, run_dir=run_dir),
        )
    validate_resource_evidence(run_dir, load_bundle(run_dir))
    completion = build_multi_host_completion(run_dir)
    atomic_install_json(
        run_dir,
        "multi-host-completion.json",
        completion,
        quarantine_root=run_dir / "quarantine",
    )
    validate_multi_host_state(run_dir, load_bundle(run_dir), require_completion=True)
    return completion


def validate_multi_host_evidence(
    run_dir: Path, bundle: Any, *, inspect_shared_root: bool = True
) -> None:
    validate_multi_host_state(
        run_dir,
        bundle,
        require_completion=True,
        inspect_shared_root=inspect_shared_root,
    )


def canonical_outcome_projection(run_dir: Path) -> bytes:
    """Return a timing-free population/verdict projection for live controls."""

    bundle = load_bundle(run_dir)
    rows = [
        {
            "result_key": row["result_key"],
            "benchmark_id": row["benchmark_id"],
            "benchmark_sha256": row["benchmark_sha256"],
            "solver_config_sha256": row["solver_config_sha256"],
            "sequence": row["sequence"],
            "expected_status": row["expected_status"],
            "observed_status": row["observed_status"],
            "reported_status": row["reported_status"],
            "verdict_admission": row["verdict_admission"],
            "termination_class": row["termination_class"],
        }
        for row in sorted(bundle.records, key=lambda value: value["sequence"])
    ]
    return canonical_bytes(rows)


def _liveness(unit: str, launcher_pid: int) -> dict[str, Any]:
    _require_safe(unit, "unit")
    completed = subprocess.run(
        ["systemctl", "--user", "is-active", unit],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        check=False,
    )
    state = completed.stdout.strip() or "unknown"
    launcher_live = True
    try:
        os.kill(launcher_pid, 0)
    except OSError as exc:
        if exc.errno == errno.ESRCH:
            launcher_live = False
        elif exc.errno != errno.EPERM:
            raise
    return {
        "unit": unit,
        "unit_state": state,
        "launcher_pid": launcher_pid,
        "launcher_live": launcher_live,
    }


def _kill_launcher(unit: str, launcher_pid: int) -> dict[str, Any]:
    _require_e3_unit(unit)
    state = _liveness(unit, launcher_pid)
    if state["unit_state"] not in {"active", "activating"} or not state["launcher_live"]:
        raise ContractError("registered launcher is not live in an active unit")
    try:
        cgroup_lines = (
            Path(f"/proc/{launcher_pid}/cgroup").read_text(encoding="ascii").splitlines()
        )
    except (OSError, UnicodeDecodeError) as exc:
        raise ContractError("cannot inspect registered launcher cgroup") from exc
    unified = [line.split("::", 1)[1] for line in cgroup_lines if line.startswith("0::")]
    if len(unified) != 1 or Path(unified[0]).name != unit:
        raise ContractError("launcher is outside the exact registered service unit")
    os.kill(launcher_pid, signal.SIGKILL)
    return {
        "unit": unit,
        "launcher_pid": launcher_pid,
        "cgroup_path": unified[0],
        "signal": signal.SIGKILL,
        "killed_at_ns": time.time_ns(),
    }


def _observe_file(path: Path) -> dict[str, Any]:
    observed_path = _require_safe_absolute_path(path, "observed_path")
    if not observed_path.is_file() or observed_path.is_symlink():
        raise ContractError("observed file is missing or not regular")
    metadata = observed_path.stat()
    if metadata.st_size > 4096:
        raise ContractError("observed file exceeds the bounded marker size")
    content = observed_path.read_bytes()
    return {
        "path": str(observed_path),
        "sha256": sha256_bytes(content),
        "bytes": len(content),
        "content_hex": content.hex(),
        "mtime_ns": metadata.st_mtime_ns,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Axeyum E3 multi-host helper")
    subparsers = parser.add_subparsers(dest="command", required=True)
    probe = subparsers.add_parser("probe")
    probe.add_argument("--shared-root", required=True)
    execute = subparsers.add_parser("execute-allocation")
    execute.add_argument("--command-manifest", required=True)
    liveness = subparsers.add_parser("liveness")
    liveness.add_argument("--unit", required=True)
    liveness.add_argument("--launcher-pid", required=True, type=int)
    kill = subparsers.add_parser("kill-launcher")
    kill.add_argument("--unit", required=True)
    kill.add_argument("--launcher-pid", required=True, type=int)
    observe = subparsers.add_parser("observe-file")
    observe.add_argument("--path", required=True)
    args = parser.parse_args()
    try:
        if args.command == "probe":
            sys.stdout.buffer.write(
                canonical_bytes(local_host_observation(Path(args.shared_root)))
            )
            return 0
        if args.command == "execute-allocation":
            return execute_host_command(Path(args.command_manifest))
        if args.command == "liveness":
            sys.stdout.buffer.write(canonical_bytes(_liveness(args.unit, args.launcher_pid)))
            return 0
        if args.command == "kill-launcher":
            sys.stdout.buffer.write(
                canonical_bytes(_kill_launcher(args.unit, args.launcher_pid))
            )
            return 0
        if args.command == "observe-file":
            sys.stdout.buffer.write(canonical_bytes(_observe_file(Path(args.path))))
            return 0
        raise ContractError("unknown E3 helper command")
    except (ContractError, OSError, ValueError) as exc:
        print(f"multi-host helper rejected: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())


__all__ = [
    "AllocationProcess",
    "COMPLETION_FIELDS",
    "PLAN_FIELDS",
    "allocation",
    "build_fault_observation",
    "build_host_command",
    "build_multi_host_completion",
    "build_plan",
    "canonical_outcome_projection",
    "close_post_run_validation_failure",
    "environment_manifest",
    "finalize_multi_host_run",
    "finish_allocation",
    "host_registration",
    "install_fault_observation",
    "kill_remote_launcher",
    "local_host_observation",
    "prepare_run_directory",
    "recover_failed_shard",
    "recover_released_failed_shard",
    "remote_probe",
    "remote_file_observation",
    "shared_filesystem_observation",
    "stage_execution_bundle",
    "start_allocation",
    "validate_execution_bundle",
    "validate_host_command",
    "validate_host_observation",
    "validate_multi_host_evidence",
    "validate_plan",
]
