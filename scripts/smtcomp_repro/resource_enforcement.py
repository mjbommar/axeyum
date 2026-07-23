"""One-host cgroup-v2 resource enforcement for resumable SMT-COMP runs.

E2 uses a transient user-systemd service as the aggregate resource boundary.
The service contains the host runner, shard workers, solver processes, and all
of their descendants.  This module validates the live kernel controller files
before a solver is launched and publishes immutable session evidence.  A
terminal is deliberately optional: SIGKILL or host loss must remain observable
as an unclosed session rather than being reconstructed after the fact.
"""

from __future__ import annotations

import copy
import os
import re
import socket
import subprocess
import time
import uuid
from pathlib import Path
from typing import Any

from resume_contract import ContractError, digest
from resume_fs import atomic_install_json, read_canonical_json


FIXTURE_RESOURCE_POLICY = {
    "stage": "E1b",
    "child_memory": "rlimit-as-best-effort",
    "peak_rss": "linux-proc-vmhwm-sampled-10ms",
    "aggregate_enforcement": "fixture-only-no-measurement-credit",
}
CGROUP_RESOURCE_POLICY = {
    "stage": "E2",
    "adapter": "systemd-user-service-cgroup-v2-v1",
    "aggregate_scope": "host-runner-shard-workers-solvers-and-descendants",
    "memory": "memory.max-exact-memory.swap.max-zero-memory.oom.group-one",
    "cpu": "cpu.max-exact-bandwidth",
    "pids": "pids.max-exact",
    "terminal_accounting": "memory.peak-memory.events-cpu.stat-pids.peak-pids.events",
}
MULTI_HOST_RESOURCE_POLICY = {
    **CGROUP_RESOURCE_POLICY,
    "stage": "E3",
    "adapter": "systemd-user-service-cgroup-v2-shared-nfs-v1",
}

FIXTURE_KIND = "fixture-e1b-no-measurement-credit"
CGROUP_KIND = "cgroup-v2-systemd-user-service-v1"
MULTI_HOST_KIND = "cgroup-v2-systemd-user-service-shared-nfs-v1"
PREFLIGHT_SCHEMA = "axeyum.smtcomp-resource-session-preflight.v1"
TERMINAL_SCHEMA = "axeyum.smtcomp-resource-session-terminal.v1"
COMPLETION_SCHEMA = "axeyum.smtcomp-resource-completion.v1"
SAFE_SESSION = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}\Z")
SAFE_UNIT_PREFIX = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,47}\Z")
SNAPSHOT_FIELDS = {
    "cgroup_path",
    "cgroup_inode",
    "controllers",
    "cgroup_type",
    "memory_max_bytes",
    "memory_swap_max_bytes",
    "memory_oom_group",
    "memory_peak_bytes",
    "memory_events",
    "cpu_quota_usec",
    "cpu_period_usec",
    "cpu_stat",
    "pids_max",
    "pids_current",
    "pids_peak",
    "pids_events",
    "member_pids",
}
PREFLIGHT_FIELDS = {
    "schema",
    "session_id",
    "run_identity_sha256",
    "enforcement_id",
    "environment_class_sha256",
    "host_id",
    "shard_ids",
    "launcher_pid",
    "started_at_ns",
    "snapshot",
    "record_sha256",
}
TERMINAL_FIELDS = {
    "schema",
    "session_id",
    "run_identity_sha256",
    "enforcement_id",
    "status",
    "worker_exit_codes",
    "memory_peak_bytes",
    "pids_peak",
    "memory_events_delta",
    "cpu_stat_delta",
    "pids_events_delta",
    "ended_at_ns",
    "record_sha256",
}
COMPLETION_FIELDS = {
    "schema",
    "run_identity_sha256",
    "enforcement_id",
    "session_ids",
    "terminal_session_ids",
    "unclosed_session_ids",
    "observed_peak_memory_bytes",
    "completed_at_ns",
    "record_sha256",
}


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    sealed = copy.deepcopy(value)
    sealed.pop("record_sha256", None)
    sealed["record_sha256"] = digest(sealed)
    return sealed


def _validate_seal(value: dict[str, Any]) -> None:
    unsealed = copy.deepcopy(value)
    claimed = unsealed.pop("record_sha256", None)
    if claimed != digest(unsealed):
        raise ContractError("resource evidence hash mismatch")


def _descriptor_id(descriptor: dict[str, Any]) -> str:
    unsealed = copy.deepcopy(descriptor)
    unsealed.pop("enforcement_id", None)
    return digest(unsealed)


def fixture_enforcement(memory_limit_bytes: int) -> dict[str, Any]:
    descriptor = {
        "kind": FIXTURE_KIND,
        "worker_slots": 1,
        "aggregate_memory_bytes": memory_limit_bytes,
    }
    descriptor["enforcement_id"] = _descriptor_id(descriptor)
    return descriptor


def cgroup_enforcement(
    *,
    worker_slots: int,
    aggregate_memory_bytes: int,
    aggregate_cpu_cores: int,
    pids_max: int,
    unit_prefix: str = "axeyum-smtcomp-e2",
    multi_host: bool = False,
) -> dict[str, Any]:
    """Build an exact E2 enforcement descriptor.

    CPU bandwidth uses systemd's default 100 ms period and an integral number
    of aggregate cores so the requested property and observed ``cpu.max`` are
    byte-unambiguous.
    """

    if not SAFE_UNIT_PREFIX.fullmatch(unit_prefix):
        raise ContractError("unsafe cgroup unit prefix")
    descriptor = {
        "kind": MULTI_HOST_KIND if multi_host else CGROUP_KIND,
        "worker_slots": worker_slots,
        "aggregate_memory_bytes": aggregate_memory_bytes,
        "aggregate_cpu_quota_usec": aggregate_cpu_cores * 100_000,
        "cpu_period_usec": 100_000,
        "pids_max": pids_max,
        "memory_swap_bytes": 0,
        "memory_oom_group": 1,
        "unit_prefix": unit_prefix,
        "required_controllers": ["cpu", "memory", "pids"],
    }
    descriptor["enforcement_id"] = _descriptor_id(descriptor)
    return descriptor


def resource_policy_for(enforcement: dict[str, Any]) -> dict[str, str]:
    kind = enforcement.get("kind")
    if kind == FIXTURE_KIND:
        return FIXTURE_RESOURCE_POLICY
    if kind == CGROUP_KIND:
        return CGROUP_RESOURCE_POLICY
    if kind == MULTI_HOST_KIND:
        return MULTI_HOST_RESOURCE_POLICY
    raise ContractError(f"unsupported aggregate resource enforcement kind: {kind}")


def validate_enforcement(
    run: dict[str, Any], *, require_measurement: bool | None = None
) -> dict[str, Any]:
    resources = run.get("resource_enforcement")
    if not isinstance(resources, dict):
        raise ContractError("missing aggregate resource enforcement")
    kind = resources.get("kind")
    fixture_fields = {
        "kind",
        "enforcement_id",
        "worker_slots",
        "aggregate_memory_bytes",
    }
    cgroup_fields = fixture_fields | {
        "aggregate_cpu_quota_usec",
        "cpu_period_usec",
        "pids_max",
        "memory_swap_bytes",
        "memory_oom_group",
        "unit_prefix",
        "required_controllers",
    }
    expected_fields = fixture_fields if kind == FIXTURE_KIND else cgroup_fields
    cgroup_kinds = {CGROUP_KIND, MULTI_HOST_KIND}
    if kind not in {FIXTURE_KIND, *cgroup_kinds} or set(resources) != expected_fields:
        raise ContractError("resource enforcement field set mismatch")
    if resources["enforcement_id"] != _descriptor_id(resources):
        raise ContractError("resource enforcement identity mismatch")
    identity = run.get("identity", {})
    workers = resources["worker_slots"]
    aggregate = resources["aggregate_memory_bytes"]
    per_worker = identity.get("memory_limit_bytes", 0)
    shard_count = identity.get("shard_count", 0)
    for field, value in (
        ("worker_slots", workers),
        ("aggregate_memory_bytes", aggregate),
        ("memory_limit_bytes", per_worker),
        ("shard_count", shard_count),
    ):
        if not isinstance(value, int) or value <= 0:
            raise ContractError(f"invalid positive resource field: {field}")
    if workers > shard_count or workers * per_worker > aggregate:
        raise ContractError("aggregate memory budget overcommitted")
    if require_measurement is True and kind not in cgroup_kinds:
        raise ContractError("measurement execution requires E2 cgroup enforcement")
    if require_measurement is False and kind != FIXTURE_KIND:
        raise ContractError("fixture execution requires fixture resource enforcement")
    if kind in cgroup_kinds:
        if not SAFE_UNIT_PREFIX.fullmatch(resources["unit_prefix"]):
            raise ContractError("unsafe cgroup unit prefix")
        required = resources["required_controllers"]
        if required != ["cpu", "memory", "pids"]:
            raise ContractError("unsupported cgroup controller set")
        for field in (
            "aggregate_cpu_quota_usec",
            "cpu_period_usec",
            "pids_max",
        ):
            if not isinstance(resources[field], int) or resources[field] <= 0:
                raise ContractError(f"invalid positive resource field: {field}")
        if resources["memory_swap_bytes"] != 0 or resources["memory_oom_group"] != 1:
            raise ContractError("E2 requires swap disabled and group OOM killing")
        required_quota = workers * identity.get("cores", 0) * resources["cpu_period_usec"]
        if resources["aggregate_cpu_quota_usec"] < required_quota:
            raise ContractError("aggregate CPU budget overcommitted")
        if resources["pids_max"] < workers * 4 + 1:
            raise ContractError("aggregate PID budget is below the worker floor")
    return resources


def _read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="ascii").strip()
    except (OSError, UnicodeDecodeError) as exc:
        raise ContractError(f"cannot read cgroup controller file: {path}") from exc


def _read_limit(path: Path) -> int | str:
    value = _read_text(path)
    if value == "max":
        return value
    try:
        parsed = int(value)
    except ValueError as exc:
        raise ContractError(f"invalid cgroup limit: {path}") from exc
    if parsed < 0:
        raise ContractError(f"negative cgroup limit: {path}")
    return parsed


def _read_counter_map(path: Path) -> dict[str, int]:
    counters: dict[str, int] = {}
    for line in _read_text(path).splitlines():
        parts = line.split()
        if len(parts) != 2 or parts[0] in counters:
            raise ContractError(f"invalid cgroup counter map: {path}")
        try:
            counters[parts[0]] = int(parts[1])
        except ValueError as exc:
            raise ContractError(f"invalid cgroup counter value: {path}") from exc
    return counters


def _current_cgroup_relative(proc_root: Path) -> str:
    lines = _read_text(proc_root / "self" / "cgroup").splitlines()
    unified = [line.split("::", 1)[1] for line in lines if line.startswith("0::")]
    if len(unified) != 1:
        raise ContractError("process is not in one cgroup-v2 hierarchy")
    relative = unified[0]
    if not relative.startswith("/") or any(part == ".." for part in relative.split("/")):
        raise ContractError("unsafe cgroup-v2 path")
    return relative


def cgroup_snapshot(
    *,
    proc_root: Path = Path("/proc"),
    cgroup_root: Path = Path("/sys/fs/cgroup"),
    expected_pid: int | None = None,
) -> dict[str, Any]:
    """Read exact live controller state for the current aggregate cgroup."""

    relative = _current_cgroup_relative(proc_root)
    directory = cgroup_root / relative.lstrip("/")
    try:
        inode = directory.stat().st_ino
    except OSError as exc:
        raise ContractError(f"missing active cgroup-v2 directory: {directory}") from exc
    cpu_parts = _read_text(directory / "cpu.max").split()
    if len(cpu_parts) != 2 or cpu_parts[0] == "max":
        raise ContractError("cgroup CPU bandwidth is not finite")
    try:
        cpu_quota, cpu_period = (int(part) for part in cpu_parts)
    except ValueError as exc:
        raise ContractError("invalid cgroup CPU bandwidth") from exc
    controllers = sorted(_read_text(directory / "cgroup.controllers").split())
    procs = sorted(
        int(line) for line in _read_text(directory / "cgroup.procs").splitlines() if line
    )
    pid = os.getpid() if expected_pid is None else expected_pid
    if pid not in procs:
        raise ContractError("host runner is outside the observed cgroup")
    return {
        "cgroup_path": relative,
        "cgroup_inode": inode,
        "controllers": controllers,
        "cgroup_type": _read_text(directory / "cgroup.type"),
        "memory_max_bytes": _read_limit(directory / "memory.max"),
        "memory_swap_max_bytes": _read_limit(directory / "memory.swap.max"),
        "memory_oom_group": _read_limit(directory / "memory.oom.group"),
        "memory_peak_bytes": _read_limit(directory / "memory.peak"),
        "memory_events": _read_counter_map(directory / "memory.events"),
        "cpu_quota_usec": cpu_quota,
        "cpu_period_usec": cpu_period,
        "cpu_stat": _read_counter_map(directory / "cpu.stat"),
        "pids_max": _read_limit(directory / "pids.max"),
        "pids_current": _read_limit(directory / "pids.current"),
        "pids_peak": _read_limit(directory / "pids.peak"),
        "pids_events": _read_counter_map(directory / "pids.events"),
        "member_pids": procs,
    }


def configure_current_cgroup(
    enforcement: dict[str, Any],
    *,
    session_id: str,
    proc_root: Path = Path("/proc"),
    cgroup_root: Path = Path("/sys/fs/cgroup"),
) -> None:
    """Apply the one delegated controller setting systemd cannot express here."""

    if enforcement.get("kind") not in {CGROUP_KIND, MULTI_HOST_KIND}:
        raise ContractError("cannot configure a non-E2 cgroup")
    snapshot = cgroup_snapshot(proc_root=proc_root, cgroup_root=cgroup_root)
    validate_snapshot(
        snapshot,
        enforcement,
        session_id=session_id,
        allow_unconfigured_oom_group=True,
    )
    target = (
        cgroup_root
        / snapshot["cgroup_path"].lstrip("/")
        / "memory.oom.group"
    )
    try:
        target.write_text(str(enforcement["memory_oom_group"]), encoding="ascii")
    except OSError as exc:
        raise ContractError("cannot configure delegated memory.oom.group") from exc
    if _read_limit(target) != enforcement["memory_oom_group"]:
        raise ContractError("delegated memory.oom.group did not retain its limit")


def validate_snapshot(
    snapshot: dict[str, Any],
    enforcement: dict[str, Any],
    *,
    session_id: str,
    allow_unconfigured_oom_group: bool = False,
) -> None:
    if set(snapshot) != SNAPSHOT_FIELDS:
        raise ContractError("cgroup snapshot field set mismatch")
    if not SAFE_SESSION.fullmatch(session_id):
        raise ContractError("unsafe resource session identity")
    path = snapshot.get("cgroup_path")
    controllers = snapshot.get("controllers")
    members = snapshot.get("member_pids")
    if (
        not isinstance(path, str)
        or not path.startswith("/")
        or any(part == ".." for part in path.split("/"))
        or type(snapshot.get("cgroup_inode")) is not int
        or snapshot["cgroup_inode"] <= 0
    ):
        raise ContractError("invalid active cgroup identity")
    if (
        not isinstance(controllers, list)
        or controllers != sorted(set(controllers))
        or any(not isinstance(controller, str) or not controller for controller in controllers)
    ):
        raise ContractError("invalid active cgroup controller set")
    if (
        not isinstance(members, list)
        or members != sorted(set(members))
        or any(type(pid) is not int or pid <= 0 for pid in members)
    ):
        raise ContractError("invalid active cgroup membership")
    required = set(enforcement["required_controllers"])
    if not required <= set(controllers):
        raise ContractError("required cgroup controller is unavailable")
    expected_unit = f"{enforcement['unit_prefix']}-{session_id}.service"
    if Path(path).name != expected_unit:
        raise ContractError("active cgroup unit identity mismatch")
    exact = {
        "memory_max_bytes": enforcement["aggregate_memory_bytes"],
        "memory_swap_max_bytes": enforcement["memory_swap_bytes"],
        "cpu_quota_usec": enforcement["aggregate_cpu_quota_usec"],
        "cpu_period_usec": enforcement["cpu_period_usec"],
        "pids_max": enforcement["pids_max"],
        "cgroup_type": "domain",
    }
    for field, expected in exact.items():
        if snapshot.get(field) != expected:
            raise ContractError(f"active cgroup limit mismatch: {field}")
    expected_oom = enforcement["memory_oom_group"]
    observed_oom = snapshot.get("memory_oom_group")
    if observed_oom != expected_oom and not (
        allow_unconfigured_oom_group and observed_oom == 0
    ):
        raise ContractError("active cgroup limit mismatch: memory_oom_group")
    for field in ("memory_peak_bytes", "pids_current", "pids_peak"):
        if type(snapshot.get(field)) is not int or snapshot[field] < 0:
            raise ContractError(f"invalid active cgroup counter: {field}")
    if snapshot["pids_current"] > enforcement["pids_max"]:
        raise ContractError("active cgroup PID usage exceeds its limit")
    for field in ("memory_events", "cpu_stat", "pids_events"):
        counters = snapshot.get(field)
        if (
            not isinstance(counters, dict)
            or not counters
            or any(
                not isinstance(key, str)
                or not key
                or type(value) is not int
                or value < 0
                for key, value in counters.items()
            )
        ):
            raise ContractError(f"invalid active cgroup counter map: {field}")


def build_preflight(
    *,
    run: dict[str, Any],
    session_id: str,
    environment_class_sha256: str,
    snapshot: dict[str, Any],
    shard_ids: list[int],
) -> dict[str, Any]:
    enforcement = validate_enforcement(run, require_measurement=True)
    validate_snapshot(snapshot, enforcement, session_id=session_id)
    identity = run["identity"]
    if environment_class_sha256 != identity["environment_class_sha256"]:
        raise ContractError("resource session environment drift")
    if (
        not shard_ids
        or shard_ids != sorted(set(shard_ids))
        or any(
            type(shard_id) is not int
            or not 0 <= shard_id < identity["shard_count"]
            for shard_id in shard_ids
        )
    ):
        raise ContractError("invalid resource session shard allocation")
    return _sealed(
        {
            "schema": PREFLIGHT_SCHEMA,
            "session_id": session_id,
            "run_identity_sha256": run["identity_sha256"],
            "enforcement_id": enforcement["enforcement_id"],
            "environment_class_sha256": environment_class_sha256,
            "host_id": socket.gethostname(),
            "shard_ids": shard_ids,
            "launcher_pid": os.getpid(),
            "started_at_ns": time.time_ns(),
            "snapshot": snapshot,
        }
    )


def _counter_delta(after: dict[str, int], before: dict[str, int]) -> dict[str, int]:
    if not set(before) <= set(after):
        raise ContractError("cgroup counter fields disappeared during execution")
    delta = {key: after[key] - value for key, value in before.items()}
    if any(value < 0 for value in delta.values()):
        raise ContractError("cgroup counter decreased during execution")
    return delta


def build_terminal(
    *,
    preflight: dict[str, Any],
    final_snapshot: dict[str, Any],
    enforcement: dict[str, Any],
    worker_exit_codes: list[int],
) -> dict[str, Any]:
    _validate_seal(preflight)
    validate_snapshot(final_snapshot, enforcement, session_id=preflight["session_id"])
    initial = preflight["snapshot"]
    if (
        final_snapshot["cgroup_path"] != initial["cgroup_path"]
        or final_snapshot["cgroup_inode"] != initial["cgroup_inode"]
    ):
        raise ContractError("resource cgroup identity changed during execution")
    memory_delta = _counter_delta(
        final_snapshot["memory_events"], initial["memory_events"]
    )
    cpu_delta = _counter_delta(final_snapshot["cpu_stat"], initial["cpu_stat"])
    pids_delta = _counter_delta(final_snapshot["pids_events"], initial["pids_events"])
    status = (
        "completed"
        if worker_exit_codes and all(code == 0 for code in worker_exit_codes)
        else "failed"
    )
    return _sealed(
        {
            "schema": TERMINAL_SCHEMA,
            "session_id": preflight["session_id"],
            "run_identity_sha256": preflight["run_identity_sha256"],
            "enforcement_id": preflight["enforcement_id"],
            "status": status,
            "worker_exit_codes": worker_exit_codes,
            "memory_peak_bytes": final_snapshot["memory_peak_bytes"],
            "pids_peak": final_snapshot["pids_peak"],
            "memory_events_delta": memory_delta,
            "cpu_stat_delta": cpu_delta,
            "pids_events_delta": pids_delta,
            "ended_at_ns": time.time_ns(),
        }
    )


def install_preflight(run_dir: Path, preflight: dict[str, Any]) -> None:
    session_id = preflight["session_id"]
    atomic_install_json(
        run_dir / "resource-sessions" / session_id,
        "preflight.json",
        preflight,
        quarantine_root=run_dir / "quarantine",
    )


def install_terminal(run_dir: Path, terminal: dict[str, Any]) -> None:
    session_id = terminal["session_id"]
    atomic_install_json(
        run_dir / "resource-sessions" / session_id,
        "terminal.json",
        terminal,
        quarantine_root=run_dir / "quarantine",
    )


def _load_sessions(run_dir: Path) -> dict[str, dict[str, Any]]:
    root = run_dir / "resource-sessions"
    if not root.is_dir():
        raise ContractError("missing E2 resource session evidence")
    sessions: dict[str, dict[str, Any]] = {}
    for directory in sorted(root.iterdir(), key=lambda path: path.name):
        if not directory.is_dir() or not SAFE_SESSION.fullmatch(directory.name):
            raise ContractError(f"unexpected resource session artifact: {directory}")
        names = {path.name for path in directory.iterdir()}
        if not names <= {"preflight.json", "terminal.json"} or "preflight.json" not in names:
            raise ContractError(f"resource session artifact set mismatch: {directory}")
        preflight = read_canonical_json(directory / "preflight.json")
        terminal = (
            read_canonical_json(directory / "terminal.json")
            if "terminal.json" in names
            else None
        )
        sessions[directory.name] = {"preflight": preflight, "terminal": terminal}
    if not sessions:
        raise ContractError("empty E2 resource session evidence")
    return sessions


def build_resource_completion(
    *, run: dict[str, Any], run_dir: Path
) -> dict[str, Any]:
    sessions = _load_sessions(run_dir)
    terminal_ids = sorted(
        session_id for session_id, value in sessions.items() if value["terminal"] is not None
    )
    unclosed = sorted(set(sessions) - set(terminal_ids))
    peaks = [
        value["terminal"]["memory_peak_bytes"]
        for value in sessions.values()
        if value["terminal"] is not None
    ]
    return _sealed(
        {
            "schema": COMPLETION_SCHEMA,
            "run_identity_sha256": run["identity_sha256"],
            "enforcement_id": run["resource_enforcement"]["enforcement_id"],
            "session_ids": sorted(sessions),
            "terminal_session_ids": terminal_ids,
            "unclosed_session_ids": unclosed,
            "observed_peak_memory_bytes": max(peaks, default=0),
            "completed_at_ns": time.time_ns(),
        }
    )


def install_resource_completion(run_dir: Path, completion: dict[str, Any]) -> None:
    atomic_install_json(
        run_dir,
        "resource-completion.json",
        completion,
        quarantine_root=run_dir / "quarantine",
    )


def _validate_preflight_record(
    preflight: dict[str, Any], run: dict[str, Any], session_id: str
) -> None:
    if set(preflight) != PREFLIGHT_FIELDS:
        raise ContractError("resource preflight field set mismatch")
    if preflight.get("schema") != PREFLIGHT_SCHEMA or preflight.get("session_id") != session_id:
        raise ContractError("resource preflight identity mismatch")
    _validate_seal(preflight)
    if preflight.get("run_identity_sha256") != run["identity_sha256"]:
        raise ContractError("resource preflight run identity mismatch")
    if preflight.get("enforcement_id") != run["resource_enforcement"]["enforcement_id"]:
        raise ContractError("resource preflight enforcement mismatch")
    if preflight.get("environment_class_sha256") != run["identity"]["environment_class_sha256"]:
        raise ContractError("resource preflight environment mismatch")
    if (
        not isinstance(preflight["host_id"], str)
        or not preflight["host_id"]
        or not isinstance(preflight["launcher_pid"], int)
        or preflight["launcher_pid"] <= 0
        or not isinstance(preflight["started_at_ns"], int)
        or preflight["started_at_ns"] < 0
    ):
        raise ContractError("invalid resource preflight process identity")
    shard_ids = preflight["shard_ids"]
    if (
        not isinstance(shard_ids, list)
        or not shard_ids
        or shard_ids != sorted(set(shard_ids))
        or any(
            type(shard_id) is not int
            or not 0 <= shard_id < run["identity"]["shard_count"]
            for shard_id in shard_ids
        )
    ):
        raise ContractError("invalid resource session shard allocation")
    if preflight["launcher_pid"] not in preflight["snapshot"]["member_pids"]:
        raise ContractError("resource preflight launcher membership mismatch")
    validate_snapshot(
        preflight["snapshot"], run["resource_enforcement"], session_id=session_id
    )


def _validate_terminal_record(
    terminal: dict[str, Any], preflight: dict[str, Any], run: dict[str, Any]
) -> None:
    if set(terminal) != TERMINAL_FIELDS:
        raise ContractError("resource terminal field set mismatch")
    if terminal.get("schema") != TERMINAL_SCHEMA:
        raise ContractError("resource terminal schema mismatch")
    _validate_seal(terminal)
    for field in ("session_id", "run_identity_sha256", "enforcement_id"):
        if terminal.get(field) != preflight.get(field):
            raise ContractError(f"resource terminal mismatch: {field}")
    if terminal.get("status") not in {"completed", "failed"}:
        raise ContractError("resource terminal status mismatch")
    codes = terminal.get("worker_exit_codes")
    if (
        not isinstance(codes, list)
        or len(codes) != len(preflight["shard_ids"])
        or any(not isinstance(code, int) for code in codes)
    ):
        raise ContractError("resource terminal worker status mismatch")
    if (terminal["status"] == "completed") != all(code == 0 for code in codes):
        raise ContractError("resource terminal completion mismatch")
    for field in ("memory_peak_bytes", "pids_peak", "ended_at_ns"):
        if not isinstance(terminal.get(field), int) or terminal[field] < 0:
            raise ContractError(f"invalid resource terminal field: {field}")
    if terminal["ended_at_ns"] < preflight["started_at_ns"]:
        raise ContractError("resource terminal predates its preflight")
    if terminal["memory_peak_bytes"] < preflight["snapshot"]["memory_peak_bytes"]:
        raise ContractError("resource memory peak decreased")
    if terminal["pids_peak"] < preflight["snapshot"]["pids_peak"]:
        raise ContractError("resource PID peak decreased")
    for field in ("memory_events_delta", "cpu_stat_delta", "pids_events_delta"):
        values = terminal.get(field)
        source = field.removesuffix("_delta")
        if not isinstance(values, dict) or any(
            not isinstance(value, int) or value < 0 for value in values.values()
        ):
            raise ContractError(f"invalid resource terminal counter map: {field}")
        if set(values) != set(preflight["snapshot"][source]):
            raise ContractError(f"resource terminal counter fields changed: {field}")


def validate_resource_session(
    *,
    run_dir: Path,
    run: dict[str, Any],
    session_id: str,
    expected_status: str | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Validate and return one closed E2 resource session."""

    sessions = _load_sessions(run_dir)
    session = sessions.get(session_id)
    if session is None:
        raise ContractError("missing exact resource session evidence")
    preflight = session["preflight"]
    terminal = session["terminal"]
    _validate_preflight_record(preflight, run, session_id)
    if terminal is None:
        raise ContractError("resource session lacks its terminal")
    _validate_terminal_record(terminal, preflight, run)
    if expected_status is not None and terminal["status"] != expected_status:
        raise ContractError("resource session terminal status mismatch")
    return preflight, terminal


def validate_resource_evidence(run_dir: Path, bundle: Any) -> None:
    """Validate all E2 session artifacts before scoring export."""

    run = bundle.run
    resources = validate_enforcement(run)
    if resources["kind"] == FIXTURE_KIND:
        if (run_dir / "resource-sessions").exists() or (
            run_dir / "resource-completion.json"
        ).exists():
            raise ContractError("fixture run contains measurement resource evidence")
        for attempts in bundle.attempts.values():
            if any(attempt.get("resource_session_id") is not None for attempt in attempts):
                raise ContractError("fixture attempt names a resource session")
        return

    sessions = _load_sessions(run_dir)
    for session_id, value in sessions.items():
        _validate_preflight_record(value["preflight"], run, session_id)
        if value["terminal"] is not None:
            _validate_terminal_record(value["terminal"], value["preflight"], run)
    referenced = {
        attempt.get("resource_session_id")
        for attempts in bundle.attempts.values()
        for attempt in attempts
    }
    if None in referenced or not referenced <= set(sessions):
        raise ContractError("attempt resource-session attribution mismatch")
    for shard_id, attempts in bundle.attempts.items():
        try:
            numeric_shard_id = int(shard_id)
        except ValueError as exc:
            raise ContractError("invalid attempt shard identity") from exc
        for attempt in attempts:
            session_id = attempt["resource_session_id"]
            if numeric_shard_id not in sessions[session_id]["preflight"]["shard_ids"]:
                raise ContractError("attempt is outside its resource-session allocation")
    completion = read_canonical_json(run_dir / "resource-completion.json")
    if set(completion) != COMPLETION_FIELDS:
        raise ContractError("resource completion field set mismatch")
    if completion.get("schema") != COMPLETION_SCHEMA:
        raise ContractError("resource completion schema mismatch")
    _validate_seal(completion)
    terminal_ids = sorted(
        session_id for session_id, value in sessions.items() if value["terminal"] is not None
    )
    unclosed = sorted(set(sessions) - set(terminal_ids))
    expected = {
        "run_identity_sha256": run["identity_sha256"],
        "enforcement_id": resources["enforcement_id"],
        "session_ids": sorted(sessions),
        "terminal_session_ids": terminal_ids,
        "unclosed_session_ids": unclosed,
    }
    for field, value in expected.items():
        if completion.get(field) != value:
            raise ContractError(f"resource completion mismatch: {field}")
    completed = [
        value["terminal"]
        for value in sessions.values()
        if value["terminal"] is not None and value["terminal"]["status"] == "completed"
    ]
    if not completed:
        raise ContractError("resource completion lacks a completed E2 session")
    peak = max(
        value["terminal"]["memory_peak_bytes"]
        for value in sessions.values()
        if value["terminal"] is not None
    )
    if completion.get("observed_peak_memory_bytes") != peak:
        raise ContractError("resource completion peak mismatch")
    if not isinstance(completion.get("completed_at_ns"), int) or completion["completed_at_ns"] < 0:
        raise ContractError("resource completion timestamp mismatch")
    latest_evidence_ns = max(
        value["terminal"]["ended_at_ns"]
        if value["terminal"] is not None
        else value["preflight"]["started_at_ns"]
        for value in sessions.values()
    )
    if completion["completed_at_ns"] < latest_evidence_ns:
        raise ContractError("resource completion predates session evidence")


def new_session_id(run_hash: str) -> str:
    return f"{run_hash[:12]}-{time.time_ns()}-{uuid.uuid4().hex[:12]}"


def systemd_run_command(
    *, enforcement: dict[str, Any], session_id: str, command: list[str]
) -> list[str]:
    if not SAFE_SESSION.fullmatch(session_id):
        raise ContractError("unsafe resource session identity")
    unit_name = f"{enforcement['unit_prefix']}-{session_id}"
    quota = enforcement["aggregate_cpu_quota_usec"]
    period = enforcement["cpu_period_usec"]
    if quota % period:
        raise ContractError("systemd adapter requires an integral CPU-core quota")
    percent = quota // period * 100
    return [
        "systemd-run",
        "--user",
        "--wait",
        "--pipe",
        "--collect",
        f"--unit={unit_name}",
        "--property=Type=exec",
        "--property=KillMode=control-group",
        f"--property=MemoryMax={enforcement['aggregate_memory_bytes']}",
        f"--property=MemorySwapMax={enforcement['memory_swap_bytes']}",
        f"--property=CPUQuota={percent}%",
        f"--property=TasksMax={enforcement['pids_max']}",
        "--property=TimeoutStopSec=5s",
        *command,
    ]


def run_under_systemd(
    *, enforcement: dict[str, Any], session_id: str, command: list[str]
) -> int:
    try:
        completed = subprocess.run(
            systemd_run_command(
                enforcement=enforcement, session_id=session_id, command=command
            ),
            check=False,
        )
    except OSError as exc:
        raise ContractError("unable to launch systemd cgroup service") from exc
    return completed.returncode


def run_worker_pool(commands: list[list[str]], worker_slots: int) -> list[int]:
    """Run shard commands with deterministic launch order and bounded overlap."""

    pending = list(enumerate(commands))
    active: list[tuple[int, subprocess.Popen[bytes]]] = []
    results: list[int | None] = [None] * len(commands)

    def stop_active() -> None:
        for _, sibling in active:
            if sibling.poll() is None:
                sibling.terminate()
        for sibling_index, sibling in active:
            try:
                results[sibling_index] = sibling.wait(timeout=5)
            except subprocess.TimeoutExpired:
                sibling.kill()
                results[sibling_index] = sibling.wait()

    while pending or active:
        while pending and len(active) < worker_slots:
            index, command = pending.pop(0)
            try:
                process = subprocess.Popen(command)
            except OSError as exc:
                stop_active()
                raise ContractError(f"unable to launch shard worker {index}") from exc
            active.append((index, process))
        completed_position = next(
            (
                position
                for position, (_, process) in enumerate(active)
                if process.poll() is not None
            ),
            None,
        )
        if completed_position is None:
            time.sleep(0.01)
            continue
        index, process = active.pop(completed_position)
        results[index] = process.returncode
        if process.returncode != 0:
            stop_active()
            for pending_index, _ in pending:
                results[pending_index] = 125
            break
    return [125 if value is None else value for value in results]


__all__ = [
    "CGROUP_KIND",
    "CGROUP_RESOURCE_POLICY",
    "COMPLETION_FIELDS",
    "FIXTURE_KIND",
    "FIXTURE_RESOURCE_POLICY",
    "MULTI_HOST_KIND",
    "MULTI_HOST_RESOURCE_POLICY",
    "PREFLIGHT_FIELDS",
    "TERMINAL_FIELDS",
    "build_preflight",
    "build_resource_completion",
    "build_terminal",
    "cgroup_enforcement",
    "cgroup_snapshot",
    "configure_current_cgroup",
    "fixture_enforcement",
    "install_preflight",
    "install_resource_completion",
    "install_terminal",
    "new_session_id",
    "resource_policy_for",
    "run_under_systemd",
    "run_worker_pool",
    "validate_enforcement",
    "validate_resource_evidence",
    "validate_resource_session",
]
