#!/usr/bin/env python3
"""Fail-closed one-attempt process adapter for Lean parity TL0.7.2.

The committed controls are synthetic and structurally unable to create case,
completion, U2, or parity credit.  TL0.7.3 owns the qualified durable store.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import platform as platform_module
import re
import resource
import signal
import socket
import stat
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[1]
PROBE = ROOT / "scripts/lean_execution_probe.py"
INVALID_INTERPRETER = ROOT / "scripts/fixtures/lean-execution-invalid-interpreter"
PREREGISTRATION_PLAN = ROOT / "docs/plan/lean-execution-process-adapter-tl0.7.2-plan-2026-07-22.md"
RESULT_AUTHORITY = ROOT / "docs/plan/lean-execution-process-v1.json"
RESULT_JSON = ROOT / "docs/plan/generated/lean-execution-process.json"
RESULT_MARKDOWN = ROOT / "docs/plan/generated/lean-execution-process.md"
SCHEMA = "axeyum-lean-process-spec-v1"
TERMINAL_SCHEMA = "axeyum-lean-process-attempt-terminal-v1"
RESULT_SCHEMA = "axeyum-lean-process-control-result-v1"
SUMMARY_SCHEMA = "axeyum-lean-process-control-summary-v1"
PREREGISTRATION_COMMIT = "45bf823a46b973a697c45140372540946edcfb0f"
EMPTY_SELECTION_ID = "synthetic-empty-selection-v1"
PROFILE = "synthetic-process-control"
CREDIT_CLASS = "synthetic-no-credit"
MEMORY_EXIT_CODE = 86
MEMORY_MARKER_PREFIX = "AXEYUM_TL0_7_2_MEMORY_LIMIT_V1"
SPEC_FIELDS = {
    "schema",
    "control_id",
    "run_id",
    "attempt_id",
    "sequence",
    "lane_id",
    "system_profile",
    "credit_class",
    "command",
    "working_directory",
    "environment",
    "source_files",
    "configuration_sha256",
    "selection_set_id",
    "assigned_case_ids",
    "wall_timeout_ms",
    "terminate_grace_ms",
    "cooperative_memory_evidence",
    "expected_terminal_class",
    "spec_sha256",
}
RUN_FIELDS = {
    "id",
    "lane_id",
    "system_profile",
    "credit_class",
    "source_sha256",
    "executable_sha256",
    "configuration_sha256",
    "command",
    "command_sha256",
    "working_directory",
    "environment",
    "environment_sha256",
    "selection_set_id",
    "selection_case_ids",
    "selection_sha256",
    "resource_envelope",
    "resource_envelope_sha256",
    "platform",
    "platform_sha256",
    "artifact_policy",
    "artifact_policy_sha256",
    "identity_sha256",
}
ATTEMPT_FIELDS = {
    "id",
    "run_id",
    "sequence",
    "recorded_before_launch",
    "assigned_case_ids",
    "terminal",
    "artifact_ids",
    "sha256",
}
TERMINAL_FIELDS = {
    "class",
    "exit_code",
    "signal",
    "events",
    "wall_time",
    "cpu_time",
    "peak_rss",
}
WRAPPER_FIELDS = {
    "schema",
    "run_id",
    "attempt_id",
    "sequence",
    "prelaunch_sha256",
    "terminal",
    "artifacts",
    "process",
    "diagnostic",
    "record_sha256",
}
LANES = {
    "standard-local-4g": {
        "memory_limit_bytes": 4_294_967_296,
        "required_mem_limit_gb": 4,
        "worker_limit": 2,
        "credit_class": "development-only",
    },
    "official-export-8g": {
        "memory_limit_bytes": 8_589_934_592,
        "required_mem_limit_gb": 8,
        "worker_limit": 1,
        "credit_class": "adapter-export-only",
    },
}
CONTROL_IDS = (
    "exit-zero-4g",
    "exit-seven-4g",
    "self-sigterm-4g",
    "wall-timeout-tree-4g",
    "memory-limit-4g",
    "memory-limit-8g",
    "invalid-interpreter-4g",
    "missing-cwd-4g",
)
EXPECTED_CLASSES = {
    "exit-zero-4g": "exited",
    "exit-seven-4g": "exited",
    "self-sigterm-4g": "signaled",
    "wall-timeout-tree-4g": "wall-timeout",
    "memory-limit-4g": "memory-limit",
    "memory-limit-8g": "memory-limit",
    "invalid-interpreter-4g": "launch-failed",
    "missing-cwd-4g": "preflight-invalid",
}
SAFE_ID = re.compile(r"[a-z0-9][a-z0-9.-]{0,127}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
HISTORICAL_RESULT_SOURCE_INPUTS = (
    {
        "path": "docs/plan/lean-execution-process-adapter-tl0.7.2-plan-2026-07-22.md",
        "sha256": "441f11cd86b50592ed038ef5b65451c74779d21d133065aa1e9213bde59d1239",
        "binding": "preregistered-current-file",
    },
    {
        "path": "scripts/lean_execution_process.py",
        "sha256": "96f6866f619563e9fc639ca360f40260d2c35b521b3fc67941675d22984b2007",
        "binding": "current-file",
    },
    {
        "path": "scripts/lean_execution_probe.py",
        "sha256": "24451fcdf9d0ff5fb0e2b7cd9e59b55d963aa12197c61c323881912f63e0b1cf",
        "binding": "current-file",
    },
    {
        "path": "scripts/fixtures/lean-execution-invalid-interpreter",
        "sha256": "2bf4485b2388353e8be93d68a669b1d255e7709f5c33b9a17cf80861ef42893b",
        "binding": "current-file",
    },
    {
        "path": "scripts/tests/test_lean_execution_process.py",
        "sha256": "5aea0fe02b3fa3278153807f7c1a1c8068ed1bfa7ea910f9b3aca08ae4a6521d",
        "binding": "current-file",
    },
)


class ProcessEvidenceError(ValueError):
    """A process spec or retained attempt failed its exact contract."""


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


def object_digest(value: dict[str, Any], hash_field: str) -> str:
    return digest({key: item for key, item in value.items() if key != hash_field})


def _metric(state: str, value: int | None, unit: str) -> dict[str, Any]:
    return {"state": state, "value": value, "unit": unit}


def _source_record(path: Path) -> dict[str, str]:
    relative = path.resolve().relative_to(ROOT).as_posix()
    return {"path": relative, "sha256": sha256_file(path)}


def historical_result_source_inputs() -> list[dict[str, str]]:
    """Return the immutable source identities of the accepted TL0.7.2 result."""
    return copy.deepcopy(list(HISTORICAL_RESULT_SOURCE_INPUTS))


def _root_for_repository_relative_path(path: str, relative: Path) -> Path | None:
    """Recover the checkout root from an absolute path and expected suffix."""
    candidate = Path(path)
    if not candidate.is_absolute() or relative.is_absolute() or ".." in relative.parts:
        return None
    for part in reversed(relative.parts):
        if candidate.name != part:
            return None
        candidate = candidate.parent
    return candidate


def _run_matches_spec_attribution(run: dict[str, Any], spec: dict[str, Any]) -> bool:
    """Compare a retained run with a live spec modulo checkout-root relocation.

    Retained process evidence deliberately preserves the absolute command that
    executed.  Validation may happen in another worktree or CI checkout, so
    repository-owned command arguments and the working directory are compared
    by their ROOT-relative suffix.  Non-repository arguments, including the
    Python executable, remain byte-exact.
    """
    run_command = run.get("command")
    spec_command = spec.get("command")
    if (
        not isinstance(run_command, list)
        or not isinstance(spec_command, list)
        or len(run_command) != len(spec_command)
    ):
        return False

    recorded_roots: set[Path] = set()
    for retained, expected in zip(run_command, spec_command, strict=True):
        if not isinstance(retained, str) or not isinstance(expected, str):
            return False
        try:
            relative = Path(expected).relative_to(ROOT)
        except ValueError:
            if retained != expected:
                return False
            continue
        recorded_root = _root_for_repository_relative_path(retained, relative)
        if recorded_root is None:
            return False
        recorded_roots.add(recorded_root)

    if len(recorded_roots) != 1:
        return False
    recorded_root = next(iter(recorded_roots))
    try:
        expected_cwd = Path(spec["working_directory"]).relative_to(ROOT)
    except (KeyError, TypeError, ValueError):
        return False
    retained_cwd_root = _root_for_repository_relative_path(
        str(run.get("working_directory", "")), expected_cwd
    )
    return retained_cwd_root == recorded_root


def _memory_marker(limit_bytes: int, mapping_bytes: int) -> str:
    return (
        f"{MEMORY_MARKER_PREFIX}|limit={limit_bytes}|"
        f"mapping={mapping_bytes}|outcome=enomem"
    )


def _seal_spec(spec: dict[str, Any]) -> dict[str, Any]:
    sealed = copy.deepcopy(spec)
    sealed["spec_sha256"] = domain_digest(
        "axeyum-lean-process-spec-v1",
        {key: value for key, value in sealed.items() if key != "spec_sha256"},
    )
    return sealed


def build_control_spec(control_id: str) -> dict[str, Any]:
    if control_id not in CONTROL_IDS:
        raise ProcessEvidenceError(f"unknown control: {control_id}")
    python = os.path.realpath(sys.executable)
    probe = str(PROBE.resolve())
    lane_id = "official-export-8g" if control_id == "memory-limit-8g" else "standard-local-4g"
    memory_limit = LANES[lane_id]["memory_limit_bytes"]
    source = PROBE
    cooperative: dict[str, Any] | None = None
    wall_timeout_ms = 2_000
    working_directory = str(ROOT)
    if control_id == "exit-zero-4g":
        command = [python, probe, "exit-zero"]
    elif control_id == "exit-seven-4g":
        command = [python, probe, "exit-seven"]
    elif control_id == "self-sigterm-4g":
        command = [python, probe, "self-sigterm"]
    elif control_id == "wall-timeout-tree-4g":
        command = [python, probe, "timeout-tree"]
    elif control_id.startswith("memory-limit-"):
        mapping_bytes = memory_limit + 1_073_741_824
        marker = _memory_marker(memory_limit, mapping_bytes)
        command = [python, probe, "memory-limit", str(memory_limit), str(mapping_bytes), marker]
        cooperative = {
            "probe_sha256": sha256_file(PROBE),
            "mode": "memory-limit",
            "limit_bytes": memory_limit,
            "mapping_bytes": mapping_bytes,
            "marker": marker,
            "exit_code": MEMORY_EXIT_CODE,
        }
        wall_timeout_ms = 5_000
    elif control_id == "invalid-interpreter-4g":
        command = [str(INVALID_INTERPRETER.resolve())]
        source = INVALID_INTERPRETER
    elif control_id == "missing-cwd-4g":
        command = [python, probe, "exit-zero"]
        working_directory = str(ROOT / ".axeyum-tl0.7.2-definitely-missing-cwd")
    else:  # pragma: no cover - CONTROL_IDS and branches are a closed pair.
        raise AssertionError(control_id)
    spec: dict[str, Any] = {
        "schema": SCHEMA,
        "control_id": control_id,
        "run_id": f"synthetic-tl0.7.2-{control_id}",
        "attempt_id": f"attempt-{control_id}",
        "sequence": 1,
        "lane_id": lane_id,
        "system_profile": PROFILE,
        "credit_class": CREDIT_CLASS,
        "command": command,
        "working_directory": working_directory,
        "environment": {"LANG": "C.UTF-8", "PYTHONHASHSEED": "0"},
        "source_files": [_source_record(source)],
        "configuration_sha256": sha256_file(Path(__file__).resolve()),
        "selection_set_id": EMPTY_SELECTION_ID,
        "assigned_case_ids": [],
        "wall_timeout_ms": wall_timeout_ms,
        "terminate_grace_ms": 250,
        "cooperative_memory_evidence": cooperative,
        "expected_terminal_class": EXPECTED_CLASSES[control_id],
        "spec_sha256": "",
    }
    return _seal_spec(spec)


def validate_spec(spec: Any, *, require_registered_control: bool = True) -> dict[str, Any]:
    if not isinstance(spec, dict) or set(spec) != SPEC_FIELDS:
        raise ProcessEvidenceError("process spec fields must be exact")
    if spec.get("schema") != SCHEMA:
        raise ProcessEvidenceError("process spec schema drift")
    control_id = spec.get("control_id")
    for field in ("control_id", "run_id", "attempt_id"):
        if not isinstance(spec.get(field), str) or not SAFE_ID.fullmatch(spec[field]):
            raise ProcessEvidenceError(f"unsafe {field}")
    claimed = spec.get("spec_sha256")
    expected_hash = domain_digest(
        "axeyum-lean-process-spec-v1",
        {key: value for key, value in spec.items() if key != "spec_sha256"},
    )
    if claimed != expected_hash:
        raise ProcessEvidenceError("process spec hash drift")
    if spec.get("system_profile") != PROFILE or spec.get("credit_class") != CREDIT_CLASS:
        raise ProcessEvidenceError("process spec cannot receive real or parity credit")
    if spec.get("lane_id") not in LANES:
        raise ProcessEvidenceError("unknown process lane")
    if spec.get("sequence") != 1:
        raise ProcessEvidenceError("TL0.7.2 control sequence must be one")
    if spec.get("selection_set_id") != EMPTY_SELECTION_ID or spec.get("assigned_case_ids") != []:
        raise ProcessEvidenceError("TL0.7.2 process controls cannot select cases")
    command = spec.get("command")
    if (
        not isinstance(command, list)
        or not command
        or not all(isinstance(item, str) and item for item in command)
        or not Path(command[0]).is_absolute()
    ):
        raise ProcessEvidenceError("command must be a nonempty absolute argument array")
    environment = spec.get("environment")
    if (
        not isinstance(environment, dict)
        or not environment
        or not all(isinstance(key, str) and key and isinstance(value, str) for key, value in environment.items())
    ):
        raise ProcessEvidenceError("environment must be a complete string mapping")
    for field in ("wall_timeout_ms", "terminate_grace_ms"):
        value = spec.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
            raise ProcessEvidenceError(f"{field} must be a positive integer")
    if spec["wall_timeout_ms"] <= spec["terminate_grace_ms"]:
        raise ProcessEvidenceError("wall timeout must exceed termination grace")
    if spec.get("configuration_sha256") != sha256_file(Path(__file__).resolve()):
        raise ProcessEvidenceError("adapter configuration identity drift")
    sources = spec.get("source_files")
    if not isinstance(sources, list) or not sources:
        raise ProcessEvidenceError("source_files must be nonempty")
    if sources != sorted(sources, key=lambda item: item.get("path", "") if isinstance(item, dict) else ""):
        raise ProcessEvidenceError("source_files must be ordered")
    for source in sources:
        if not isinstance(source, dict) or set(source) != {"path", "sha256"}:
            raise ProcessEvidenceError("source record fields must be exact")
        path_text = source.get("path")
        if not isinstance(path_text, str) or Path(path_text).is_absolute() or ".." in Path(path_text).parts:
            raise ProcessEvidenceError("source path must be repository-relative")
        path = (ROOT / path_text).resolve()
        try:
            path.relative_to(ROOT)
        except ValueError as exc:
            raise ProcessEvidenceError("source path escapes repository") from exc
        if not path.is_file() or source.get("sha256") != sha256_file(path):
            raise ProcessEvidenceError("source content identity drift")
    cooperative = spec.get("cooperative_memory_evidence")
    if cooperative is not None:
        required = {
            "probe_sha256",
            "mode",
            "limit_bytes",
            "mapping_bytes",
            "marker",
            "exit_code",
        }
        if not isinstance(cooperative, dict) or set(cooperative) != required:
            raise ProcessEvidenceError("cooperative memory evidence fields must be exact")
        lane_limit = LANES[spec["lane_id"]]["memory_limit_bytes"]
        if (
            cooperative.get("probe_sha256") != sha256_file(PROBE)
            or cooperative.get("mode") != "memory-limit"
            or cooperative.get("limit_bytes") != lane_limit
            or not isinstance(cooperative.get("mapping_bytes"), int)
            or cooperative["mapping_bytes"] <= lane_limit
            or cooperative.get("marker") != _memory_marker(lane_limit, cooperative["mapping_bytes"])
            or cooperative.get("exit_code") != MEMORY_EXIT_CODE
            or command
            != [
                os.path.realpath(sys.executable),
                str(PROBE.resolve()),
                "memory-limit",
                str(lane_limit),
                str(cooperative["mapping_bytes"]),
                cooperative["marker"],
            ]
        ):
            raise ProcessEvidenceError("cooperative memory evidence identity drift")
    if spec.get("expected_terminal_class") not in {
        "exited",
        "signaled",
        "wall-timeout",
        "memory-limit",
        "launch-failed",
        "preflight-invalid",
    }:
        raise ProcessEvidenceError("unsupported expected terminal class")
    if require_registered_control:
        if control_id not in CONTROL_IDS or spec != build_control_spec(control_id):
            raise ProcessEvidenceError("registered control bytes drifted")
    return copy.deepcopy(spec)


def read_canonical_spec(path: Path) -> dict[str, Any]:
    try:
        raw = path.read_bytes()
        value = json.loads(raw)
    except (OSError, json.JSONDecodeError) as exc:
        raise ProcessEvidenceError(f"cannot read process spec: {path}") from exc
    if raw != canonical_bytes(value):
        raise ProcessEvidenceError("process spec is not canonical JSON")
    return validate_spec(value)


def _filesystem_identity(path: Path) -> str:
    stat_result = path.stat()
    vfs = os.statvfs(path)
    return f"st_dev={stat_result.st_dev};f_fsid={vfs.f_fsid};f_bsize={vfs.f_bsize}"


def _read_first_cpu_model() -> str:
    try:
        for line in Path("/proc/cpuinfo").read_text(encoding="utf-8", errors="replace").splitlines():
            if line.startswith(("model name", "Hardware", "Processor")) and ":" in line:
                return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return platform_module.processor() or "not-observed"


def _os_image() -> str:
    try:
        values = {}
        for line in Path("/etc/os-release").read_text(encoding="utf-8").splitlines():
            if "=" in line:
                key, value = line.split("=", 1)
                values[key] = value.strip().strip('"')
        return values.get("PRETTY_NAME") or values.get("ID") or "not-observed"
    except OSError:
        return "not-observed"


def capture_platform(working_directory: Path) -> dict[str, Any]:
    pages = os.sysconf("SC_PHYS_PAGES")
    page_size = os.sysconf("SC_PAGE_SIZE")
    return {
        "provider": "local-process",
        "runner_label": "local-unlabelled",
        "runner_id": socket.gethostname(),
        "os": platform_module.system(),
        "architecture": platform_module.machine(),
        "kernel": platform_module.release(),
        "image": _os_image(),
        "cpu": _read_first_cpu_model(),
        "memory_bytes": pages * page_size,
        "filesystem": _filesystem_identity(working_directory if working_directory.is_dir() else ROOT),
    }


def _resource_envelope(spec: dict[str, Any]) -> dict[str, Any]:
    lane = LANES[spec["lane_id"]]
    return {
        "lane_id": spec["lane_id"],
        "memory_limit": _metric("observed", lane["memory_limit_bytes"], "bytes"),
        "memory_scope": "per-process-address-space",
        "memory_enforcement": "explicit-rlimit-as",
        "explicit_mem_limit_gb": lane["required_mem_limit_gb"],
        "wall_timeout": _metric("observed", spec["wall_timeout_ms"], "milliseconds"),
        "cpu_time_limit": _metric("not-enforced", None, "seconds"),
        "worker_limit": _metric("observed", 1, "workers"),
        "thread_limit": _metric("observed", 1, "threads"),
        "process_limit": _metric("not-enforced", None, "processes"),
        "pids_limit": _metric("not-enforced", None, "pids"),
        "swap_limit": _metric("not-enforced", None, "bytes"),
        "disk_limit": _metric("not-enforced", None, "bytes"),
        "open_file_limit": _metric("not-observed", None, "files"),
        "requested_parallelism": 1,
        "effective_parallelism": 1,
        "enforcement_artifact_ids": ["attempt-terminal", "process-adapter-source"],
    }


def _build_run(spec: dict[str, Any]) -> dict[str, Any]:
    command = spec["command"]
    executable = Path(command[0])
    resources = _resource_envelope(spec)
    actual_platform = capture_platform(Path(spec["working_directory"]))
    artifact_policy = {
        "canonical_json": True,
        "content_hashed_raw_output": True,
        "new_output_directory_required": True,
        "completion_permitted": False,
        "durability_qualified": False,
        "durability_owner": "TL0.7.3",
    }
    run: dict[str, Any] = {
        "id": spec["run_id"],
        "lane_id": spec["lane_id"],
        "system_profile": spec["system_profile"],
        "credit_class": spec["credit_class"],
        "source_sha256": domain_digest("axeyum-lean-process-source-set-v1", spec["source_files"]),
        "executable_sha256": sha256_file(executable),
        "configuration_sha256": spec["configuration_sha256"],
        "command": command,
        "command_sha256": digest(command),
        "working_directory": spec["working_directory"],
        "environment": spec["environment"],
        "environment_sha256": digest(spec["environment"]),
        "selection_set_id": spec["selection_set_id"],
        "selection_case_ids": spec["assigned_case_ids"],
        "selection_sha256": digest(spec["assigned_case_ids"]),
        "resource_envelope": resources,
        "resource_envelope_sha256": digest(resources),
        "platform": actual_platform,
        "platform_sha256": digest(actual_platform),
        "artifact_policy": artifact_policy,
        "artifact_policy_sha256": digest(artifact_policy),
        "identity_sha256": "",
    }
    run["identity_sha256"] = object_digest(run, "identity_sha256")
    return run


def _build_prelaunch(spec: dict[str, Any]) -> dict[str, Any]:
    attempt: dict[str, Any] = {
        "id": spec["attempt_id"],
        "run_id": spec["run_id"],
        "sequence": spec["sequence"],
        "recorded_before_launch": True,
        "assigned_case_ids": [],
        "terminal": None,
        "artifact_ids": ["stderr", "stdout"],
        "sha256": "",
    }
    attempt["sha256"] = object_digest(attempt, "sha256")
    return attempt


def _write_exclusive(path: Path, content: bytes) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    descriptor = os.open(path, flags, 0o644)
    try:
        offset = 0
        while offset < len(content):
            offset += os.write(descriptor, content[offset:])
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    directory = os.open(path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def _create_output_directory(path: Path) -> None:
    try:
        path.mkdir(mode=0o755, parents=False, exist_ok=False)
    except OSError as exc:
        raise ProcessEvidenceError(f"output directory must be new: {path}") from exc


def _sample_peak_rss(pid: int) -> int | None:
    try:
        values: dict[str, int] = {}
        for line in Path(f"/proc/{pid}/status").read_text(encoding="ascii").splitlines():
            if line.startswith(("VmHWM:", "VmRSS:")):
                parts = line.split()
                if len(parts) == 3 and parts[2] == "kB":
                    values[parts[0].rstrip(":")] = int(parts[1]) * 1024
        value = values.get("VmHWM") or values.get("VmRSS")
        return value if value and value > 0 else None
    except (OSError, UnicodeDecodeError, ValueError):
        return None


def _live_process_group_members(pgid: int) -> list[int]:
    live: list[int] = []
    try:
        entries = list(Path("/proc").iterdir())
    except OSError as exc:
        raise ProcessEvidenceError("cannot inspect /proc for process-group cleanup") from exc
    for entry in entries:
        if not entry.name.isdigit():
            continue
        try:
            text = (entry / "stat").read_text(encoding="ascii")
            tail = text[text.rfind(")") + 2 :].split()
            state = tail[0]
            member_group = int(tail[2])
        except (OSError, UnicodeDecodeError, ValueError, IndexError):
            continue
        if member_group == pgid and state != "Z":
            live.append(int(entry.name))
    return sorted(live)


def _preflight_reason(spec: dict[str, Any]) -> str | None:
    if platform_module.system() != "Linux" or not Path("/proc/self/status").is_file():
        return "linux-proc-required"
    working_directory = Path(spec["working_directory"])
    if not working_directory.is_dir():
        return "missing-working-directory"
    executable = Path(spec["command"][0])
    if not executable.is_file() or not os.access(executable, os.X_OK):
        return "invalid-executable"
    if not hasattr(resource, "RLIMIT_AS"):
        return "rlimit-as-unavailable"
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    requested = LANES[spec["lane_id"]]["memory_limit_bytes"]
    if hard != resource.RLIM_INFINITY and hard < requested:
        return "rlimit-as-hard-limit-too-low"
    return None


def _limit_hook(limit_bytes: int) -> Callable[[], None]:
    def install() -> None:
        resource.setrlimit(resource.RLIMIT_AS, (limit_bytes, limit_bytes))

    return install


def _raw_artifact(artifact_id: str, path: Path) -> dict[str, Any]:
    return {
        "id": artifact_id,
        "kind": artifact_id,
        "sha256": sha256_file(path),
        "bytes": path.stat().st_size,
    }


def _terminal_wrapper(
    spec: dict[str, Any],
    prelaunch: dict[str, Any],
    terminal: dict[str, Any],
    stdout_path: Path,
    stderr_path: Path,
    process: dict[str, Any],
    diagnostic: dict[str, Any] | None,
) -> dict[str, Any]:
    wrapper: dict[str, Any] = {
        "schema": TERMINAL_SCHEMA,
        "run_id": spec["run_id"],
        "attempt_id": spec["attempt_id"],
        "sequence": spec["sequence"],
        "prelaunch_sha256": prelaunch["sha256"],
        "terminal": terminal,
        "artifacts": [_raw_artifact("stderr", stderr_path), _raw_artifact("stdout", stdout_path)],
        "process": process,
        "diagnostic": diagnostic,
        "record_sha256": "",
    }
    wrapper["record_sha256"] = domain_digest(
        TERMINAL_SCHEMA,
        {key: value for key, value in wrapper.items() if key != "record_sha256"},
    )
    return wrapper


def _write_adapter_diagnostic(handle: Any, kind: str, detail: str) -> dict[str, str]:
    line = f"AXEYUM_TL0_7_2_{kind.upper().replace('-', '_')}_V1|reason={detail}\n".encode()
    handle.write(line)
    handle.flush()
    os.fsync(handle.fileno())
    return {"kind": kind, "message_sha256": sha256_bytes(line)}


def _cooperative_memory_matches(
    spec: dict[str, Any], return_code: int | None, stderr_bytes: bytes
) -> bool:
    evidence = spec.get("cooperative_memory_evidence")
    if not isinstance(evidence, dict) or return_code != evidence["exit_code"]:
        return False
    marker = (evidence["marker"] + "\n").encode()
    if stderr_bytes.count(marker) != 1:
        return False
    return evidence["probe_sha256"] == sha256_file(PROBE)


def execute_spec(
    spec: dict[str, Any],
    output_directory: Path,
    *,
    popen_factory: Callable[..., subprocess.Popen[bytes]] = subprocess.Popen,
) -> dict[str, Any]:
    validated = validate_spec(spec)
    output_directory = output_directory.resolve()
    if output_directory.parent == output_directory:
        raise ProcessEvidenceError("unsafe output directory")
    _create_output_directory(output_directory)
    run = _build_run(validated)
    prelaunch = _build_prelaunch(validated)
    run_path = output_directory / "run.json"
    stdout_path = output_directory / "stdout.bin"
    stderr_path = output_directory / "stderr.bin"
    prelaunch_path = output_directory / "attempt-prelaunch.json"
    terminal_path = output_directory / "attempt-terminal.json"
    _write_exclusive(run_path, canonical_bytes(run))
    stdout_handle = stdout_path.open("xb", buffering=0)
    stderr_handle = stderr_path.open("xb", buffering=0)
    _write_exclusive(prelaunch_path, canonical_bytes(prelaunch))

    termination_class: str
    exit_code: int | None = None
    terminating_signal: int | None = None
    events: list[str] = []
    wall_metric = _metric("not-observed", None, "milliseconds")
    peak_metric = _metric("not-observed", None, "bytes")
    diagnostic: dict[str, str] | None = None
    pid: int | None = None
    pgid: int | None = None
    watchdog_fired = False
    sigterm_sent = False
    sigkill_sent = False
    direct_child_reaped = False
    live_after_cleanup: list[int] = []
    installed_limit: int | None = None
    process: subprocess.Popen[bytes] | None = None
    peak_rss: int | None = None
    preflight_reason = _preflight_reason(validated)
    if preflight_reason is not None:
        termination_class = "preflight-invalid"
        events.append("preflight-invalid-observed")
        diagnostic = _write_adapter_diagnostic(stderr_handle, "preflight-invalid", preflight_reason)
    else:
        memory_limit = LANES[validated["lane_id"]]["memory_limit_bytes"]
        start_ns = time.monotonic_ns()
        try:
            process = popen_factory(
                validated["command"],
                stdin=subprocess.DEVNULL,
                stdout=stdout_handle,
                stderr=stderr_handle,
                cwd=validated["working_directory"],
                env=validated["environment"],
                shell=False,
                close_fds=True,
                start_new_session=True,
                preexec_fn=_limit_hook(memory_limit),
            )
        except (OSError, subprocess.SubprocessError) as exc:
            termination_class = "launch-failed"
            detail = f"{type(exc).__name__}-errno-{getattr(exc, 'errno', None)}"
            events.append("launch-error-observed")
            diagnostic = _write_adapter_diagnostic(stderr_handle, "launch-failed", detail)
        else:
            pid = process.pid
            pgid = process.pid
            installed_limit = memory_limit
            events.append("rlimit-as-installed")
            deadline_ns = start_ns + validated["wall_timeout_ms"] * 1_000_000
            while process.poll() is None and time.monotonic_ns() < deadline_ns:
                sampled = _sample_peak_rss(pid)
                if sampled is not None:
                    peak_rss = max(peak_rss or 0, sampled)
                time.sleep(0.01)
            if process.poll() is None:
                watchdog_fired = True
                events.append("wall-timeout-observed")
                try:
                    os.killpg(pgid, signal.SIGTERM)
                    sigterm_sent = True
                    events.append("process-group-sigterm-sent")
                except ProcessLookupError:
                    pass
                grace_deadline = time.monotonic_ns() + validated["terminate_grace_ms"] * 1_000_000
                while time.monotonic_ns() < grace_deadline:
                    if not _live_process_group_members(pgid):
                        break
                    time.sleep(0.01)
                live_before_kill = _live_process_group_members(pgid)
                if live_before_kill:
                    try:
                        os.killpg(pgid, signal.SIGKILL)
                        sigkill_sent = True
                        events.append("process-group-sigkill-sent")
                    except ProcessLookupError:
                        pass
            try:
                process.wait(timeout=2.0)
                direct_child_reaped = True
                events.append("direct-child-reaped")
            except subprocess.TimeoutExpired:
                if pgid is not None:
                    try:
                        os.killpg(pgid, signal.SIGKILL)
                        sigkill_sent = True
                        if "process-group-sigkill-sent" not in events:
                            events.append("process-group-sigkill-sent")
                    except ProcessLookupError:
                        pass
                process.kill()
                process.wait(timeout=2.0)
                direct_child_reaped = True
                events.append("direct-child-reaped")
            sampled = _sample_peak_rss(pid)
            if sampled is not None:
                peak_rss = max(peak_rss or 0, sampled)
            if pgid is not None:
                cleanup_deadline = time.monotonic_ns() + 1_000_000_000
                while time.monotonic_ns() < cleanup_deadline:
                    live_after_cleanup = _live_process_group_members(pgid)
                    if not live_after_cleanup:
                        break
                    time.sleep(0.01)
                if not live_after_cleanup:
                    events.append("process-group-no-live-members-observed")
            elapsed_ms = max(1, (time.monotonic_ns() - start_ns) // 1_000_000)
            wall_metric = _metric("observed", elapsed_ms, "milliseconds")
            if peak_rss is not None:
                peak_metric = _metric("observed", peak_rss, "bytes")
            return_code = process.returncode
            stderr_handle.flush()
            os.fsync(stderr_handle.fileno())
            stderr_bytes = stderr_path.read_bytes()
            if watchdog_fired:
                termination_class = "wall-timeout"
                terminating_signal = -return_code if return_code is not None and return_code < 0 else None
            elif _cooperative_memory_matches(validated, return_code, stderr_bytes):
                termination_class = "memory-limit"
                events.append("memory-limit-observed")
                events.append("cooperative-memory-diagnostic-observed")
                exit_code = return_code
            elif return_code is not None and return_code < 0:
                termination_class = "signaled"
                terminating_signal = -return_code
                events.append("signal-observed")
            else:
                termination_class = "exited"
                exit_code = return_code
                events.append("exit-status-observed")

    stdout_handle.flush()
    stderr_handle.flush()
    os.fsync(stdout_handle.fileno())
    os.fsync(stderr_handle.fileno())
    stdout_handle.close()
    stderr_handle.close()
    terminal = {
        "class": termination_class,
        "exit_code": exit_code,
        "signal": terminating_signal,
        "events": events,
        "wall_time": wall_metric,
        "cpu_time": _metric("not-observed", None, "milliseconds"),
        "peak_rss": peak_metric,
    }
    process_record = {
        "pid": pid,
        "process_group_id": pgid,
        "rlimit_as_bytes": installed_limit,
        "watchdog_fired": watchdog_fired,
        "sigterm_sent": sigterm_sent,
        "sigkill_sent": sigkill_sent,
        "direct_child_reaped": direct_child_reaped,
        "live_non_zombie_pids_after_cleanup": live_after_cleanup,
    }
    wrapper = _terminal_wrapper(
        validated,
        prelaunch,
        terminal,
        stdout_path,
        stderr_path,
        process_record,
        diagnostic,
    )
    _write_exclusive(terminal_path, canonical_bytes(wrapper))
    failures = validate_attempt_directory(output_directory, expected_spec=validated)
    if failures:
        raise ProcessEvidenceError("; ".join(failures))
    return wrapper


def _load_canonical(path: Path) -> Any:
    try:
        raw = path.read_bytes()
        value = json.loads(raw)
    except (OSError, json.JSONDecodeError) as exc:
        raise ProcessEvidenceError(f"cannot load retained record: {path}") from exc
    if raw != canonical_bytes(value):
        raise ProcessEvidenceError(f"retained JSON is not canonical: {path}")
    return value


def validate_attempt_directory(
    directory: Path, *, expected_spec: dict[str, Any] | None = None
) -> list[str]:
    failures: list[str] = []
    expected_names = {
        "run.json",
        "stdout.bin",
        "stderr.bin",
        "attempt-prelaunch.json",
        "attempt-terminal.json",
    }
    try:
        names = {item.name for item in directory.iterdir()}
    except OSError as exc:
        return [f"cannot enumerate attempt directory: {exc}"]
    if names != expected_names:
        failures.append("attempt directory file set must be exact")
        return failures
    try:
        run = _load_canonical(directory / "run.json")
        prelaunch = _load_canonical(directory / "attempt-prelaunch.json")
        wrapper = _load_canonical(directory / "attempt-terminal.json")
    except ProcessEvidenceError as exc:
        return [str(exc)]
    if not isinstance(run, dict) or set(run) != RUN_FIELDS:
        failures.append("run fields must be exact")
    elif run.get("identity_sha256") != object_digest(run, "identity_sha256"):
        failures.append("run identity hash drift")
    else:
        for field, value in (
            ("command_sha256", run.get("command")),
            ("environment_sha256", run.get("environment")),
            ("selection_sha256", run.get("selection_case_ids")),
            ("resource_envelope_sha256", run.get("resource_envelope")),
            ("platform_sha256", run.get("platform")),
            ("artifact_policy_sha256", run.get("artifact_policy")),
        ):
            if run.get(field) != digest(value):
                failures.append(f"run {field} drift")
    if not isinstance(prelaunch, dict) or set(prelaunch) != ATTEMPT_FIELDS:
        failures.append("prelaunch attempt fields must be exact")
    elif (
        prelaunch.get("recorded_before_launch") is not True
        or prelaunch.get("terminal") is not None
        or prelaunch.get("assigned_case_ids") != []
        or prelaunch.get("artifact_ids") != ["stderr", "stdout"]
        or prelaunch.get("sha256") != object_digest(prelaunch, "sha256")
    ):
        failures.append("prelaunch attempt contract drift")
    if not isinstance(wrapper, dict) or set(wrapper) != WRAPPER_FIELDS:
        failures.append("terminal wrapper fields must be exact")
        return failures
    claimed = wrapper.get("record_sha256")
    expected = domain_digest(
        TERMINAL_SCHEMA,
        {key: value for key, value in wrapper.items() if key != "record_sha256"},
    )
    if wrapper.get("schema") != TERMINAL_SCHEMA or claimed != expected:
        failures.append("terminal wrapper identity drift")
    if isinstance(prelaunch, dict) and wrapper.get("prelaunch_sha256") != prelaunch.get("sha256"):
        failures.append("terminal does not reference exact prelaunch record")
    terminal = wrapper.get("terminal")
    if not isinstance(terminal, dict) or set(terminal) != TERMINAL_FIELDS:
        failures.append("terminal fields must be exact")
    else:
        for field in ("wall_time", "cpu_time", "peak_rss"):
            metric = terminal.get(field)
            if not isinstance(metric, dict) or set(metric) != {"state", "value", "unit"}:
                failures.append(f"{field} metric fields must be exact")
            elif metric.get("state") in {"not-observed", "not-enforced"} and metric.get("value") is not None:
                failures.append(f"{field} missing metric must use null")
            elif metric.get("state") == "observed" and (
                not isinstance(metric.get("value"), int) or isinstance(metric.get("value"), bool) or metric["value"] < 0
            ):
                failures.append(f"{field} observed metric must be a nonnegative integer")
    artifacts = wrapper.get("artifacts")
    expected_artifacts = [
        _raw_artifact("stderr", directory / "stderr.bin"),
        _raw_artifact("stdout", directory / "stdout.bin"),
    ]
    if artifacts != expected_artifacts:
        failures.append("raw artifact identity drift")
    if expected_spec is not None:
        try:
            spec = validate_spec(expected_spec)
        except ProcessEvidenceError as exc:
            failures.append(str(exc))
            return failures
        if run.get("id") != spec["run_id"] or not _run_matches_spec_attribution(
            run, spec
        ):
            failures.append("run/spec attribution drift")
        if (
            prelaunch.get("id") != spec["attempt_id"]
            or wrapper.get("run_id") != spec["run_id"]
            or wrapper.get("attempt_id") != spec["attempt_id"]
            or wrapper.get("sequence") != spec["sequence"]
        ):
            failures.append("attempt/spec attribution drift")
        if terminal.get("class") != spec["expected_terminal_class"]:
            failures.append("terminal class differs from preregistered control")
        process = wrapper.get("process")
        if not isinstance(process, dict) or set(process) != {
            "pid",
            "process_group_id",
            "rlimit_as_bytes",
            "watchdog_fired",
            "sigterm_sent",
            "sigkill_sent",
            "direct_child_reaped",
            "live_non_zombie_pids_after_cleanup",
        }:
            failures.append("process observation fields must be exact")
        elif terminal.get("class") in {"exited", "signaled", "wall-timeout", "memory-limit"}:
            if process.get("rlimit_as_bytes") != LANES[spec["lane_id"]]["memory_limit_bytes"]:
                failures.append("effective RLIMIT_AS evidence drift")
            if process.get("direct_child_reaped") is not True:
                failures.append("direct child was not reaped")
            if process.get("live_non_zombie_pids_after_cleanup") != []:
                failures.append("live descendant survived process-group cleanup")
        if terminal.get("class") == "wall-timeout":
            if terminal.get("events", []).count("wall-timeout-observed") != 1:
                failures.append("wall timeout lacks unique watchdog evidence")
            if not process.get("watchdog_fired") or not process.get("sigterm_sent"):
                failures.append("wall timeout cleanup evidence incomplete")
        if terminal.get("class") == "memory-limit":
            stderr = (directory / "stderr.bin").read_bytes()
            if not _cooperative_memory_matches(spec, terminal.get("exit_code"), stderr):
                failures.append("memory limit lacks exact cooperative evidence")
            if terminal.get("events", []).count("memory-limit-observed") != 1:
                failures.append("memory limit event evidence drift")
    return failures


def write_control_spec(control_id: str, path: Path) -> None:
    _write_exclusive(path, canonical_bytes(build_control_spec(control_id)))


def _evidence_file_manifest(evidence_root: Path) -> list[dict[str, Any]]:
    rows = []
    for path in sorted(item for item in evidence_root.rglob("*") if item.is_file()):
        rows.append(
            {
                "path": path.relative_to(ROOT).as_posix(),
                "bytes": path.stat().st_size,
                "sha256": sha256_file(path),
            }
        )
    return rows


def build_result_authority(
    evidence_root: Path, *, implementation_revision: str
) -> dict[str, Any]:
    evidence_root = evidence_root.resolve()
    if not re.fullmatch(r"[0-9a-f]{40}", implementation_revision):
        raise ProcessEvidenceError("implementation revision must be lowercase 40-hex")
    try:
        relative_evidence_root = evidence_root.relative_to(ROOT).as_posix()
    except ValueError as exc:
        raise ProcessEvidenceError("retained evidence must be inside the repository") from exc
    try:
        directory_names = sorted(path.name for path in evidence_root.iterdir() if path.is_dir())
        nondirectories = [path.name for path in evidence_root.iterdir() if not path.is_dir()]
    except OSError as exc:
        raise ProcessEvidenceError("cannot enumerate retained process evidence") from exc
    if directory_names != sorted(CONTROL_IDS) or nondirectories:
        raise ProcessEvidenceError("retained control directory set must be exact")
    controls = []
    classification_counts: dict[str, int] = {}
    for control_id in CONTROL_IDS:
        directory = evidence_root / control_id
        spec = build_control_spec(control_id)
        failures = validate_attempt_directory(directory, expected_spec=spec)
        if failures:
            raise ProcessEvidenceError(f"{control_id}: {'; '.join(failures)}")
        run = _load_canonical(directory / "run.json")
        prelaunch = _load_canonical(directory / "attempt-prelaunch.json")
        wrapper = _load_canonical(directory / "attempt-terminal.json")
        terminal = wrapper["terminal"]
        classification = terminal["class"]
        classification_counts[classification] = classification_counts.get(classification, 0) + 1
        controls.append(
            {
                "control_id": control_id,
                "lane_id": spec["lane_id"],
                "run_id": run["id"],
                "run_identity_sha256": run["identity_sha256"],
                "platform_sha256": run["platform_sha256"],
                "attempt_id": prelaunch["id"],
                "prelaunch_sha256": prelaunch["sha256"],
                "expected_terminal_class": spec["expected_terminal_class"],
                "observed_terminal_class": classification,
                "exit_code": terminal["exit_code"],
                "signal": terminal["signal"],
                "events": terminal["events"],
                "wall_time": terminal["wall_time"],
                "cpu_time": terminal["cpu_time"],
                "peak_rss": terminal["peak_rss"],
                "rlimit_as_bytes": wrapper["process"]["rlimit_as_bytes"],
                "watchdog_fired": wrapper["process"]["watchdog_fired"],
                "sigterm_sent": wrapper["process"]["sigterm_sent"],
                "sigkill_sent": wrapper["process"]["sigkill_sent"],
                "direct_child_reaped": wrapper["process"]["direct_child_reaped"],
                "live_non_zombie_pids_after_cleanup": wrapper["process"][
                    "live_non_zombie_pids_after_cleanup"
                ],
                "raw_artifacts": wrapper["artifacts"],
                "terminal_record_sha256": wrapper["record_sha256"],
            }
        )
    expected_counts = {
        "exited": 2,
        "signaled": 1,
        "wall-timeout": 1,
        "memory-limit": 2,
        "launch-failed": 1,
        "preflight-invalid": 1,
    }
    if classification_counts != expected_counts:
        raise ProcessEvidenceError("retained terminal-class partition drift")
    source_inputs = historical_result_source_inputs()
    files = _evidence_file_manifest(evidence_root)
    authority: dict[str, Any] = {
        "schema": RESULT_SCHEMA,
        "as_of": "2026-07-22",
        "scope": "synthetic-process-controls-only-no-lean-u2-case-completion-or-parity-credit",
        "preregistration": {
            "plan_commit": PREREGISTRATION_COMMIT,
            "plan_sha256": sha256_file(PREREGISTRATION_PLAN),
            "implementation_revision": implementation_revision,
            "plan_published_before_implementation": True,
            "implementation_published_before_retained_result": True,
        },
        "source_inputs": source_inputs,
        "evidence_root": relative_evidence_root,
        "evidence_files": files,
        "controls": controls,
        "summary": {
            "registered_controls": len(CONTROL_IDS),
            "retained_process_attempts": len(controls),
            "classification_counts": classification_counts,
            "lane_counts": {
                "standard-local-4g": 7,
                "official-export-8g": 1,
            },
            "raw_artifacts": len(controls) * 2,
            "retained_files": len(files),
            "retained_bytes": sum(row["bytes"] for row in files),
            "case_records": 0,
            "completion_records": 0,
            "junit_artifacts": 0,
            "provider_artifacts": 0,
        },
        "credits": {
            "real_runs": 0,
            "official_outcomes": 0,
            "axeyum_outcomes": 0,
            "completed_cases": 0,
            "paired_cells": 0,
            "performance_rows": 0,
            "parity_credit": 0,
        },
        "milestones": [
            {"id": "TL0.7.1", "state": "done"},
            {"id": "TL0.7.2", "state": "synthetic-process-controls-complete"},
            {"id": "TL0.7.3", "state": "not-run"},
            {"id": "TL0.7.4", "state": "not-run"},
            {"id": "TL0.6.3", "state": "blocked-on-tl0.7"},
        ],
        "residual": [
            "Qualify immutable checkpoint installation, conflict quarantine, kill/resume, and completion-last publication in TL0.7.3.",
            "Run the two no-credit real controls only after TL0.7.3 in TL0.7.4.",
            "Keep every U2 official and Axeyum outcome at zero until TL0.6.3 begins.",
        ],
        "authority_sha256": "",
    }
    authority["authority_sha256"] = domain_digest(
        RESULT_SCHEMA,
        {key: value for key, value in authority.items() if key != "authority_sha256"},
    )
    return authority


def validate_result_authority(authority: Any) -> list[str]:
    failures: list[str] = []
    if not isinstance(authority, dict):
        return ["result authority must be an object"]
    preregistration = authority.get("preregistration")
    implementation_revision = (
        preregistration.get("implementation_revision")
        if isinstance(preregistration, dict)
        else None
    )
    evidence_root = authority.get("evidence_root")
    if not isinstance(evidence_root, str):
        return ["result authority evidence root is missing"]
    try:
        expected = build_result_authority(
            ROOT / evidence_root, implementation_revision=str(implementation_revision)
        )
    except ProcessEvidenceError as exc:
        return [str(exc)]
    if authority != expected:
        failures.append("result authority differs from retained process evidence")
    return failures


def build_result_summary(authority: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": SUMMARY_SCHEMA,
        "authority_sha256": authority["authority_sha256"],
        "scope": authority["scope"],
        "summary": authority["summary"],
        "credits": authority["credits"],
        "controls": authority["controls"],
        "milestones": authority["milestones"],
        "residual": authority["residual"],
    }


def render_result_markdown(authority: dict[str, Any]) -> str:
    summary = authority["summary"]
    lines = [
        "# Generated TL0.7.2 Lean process-control result",
        "",
        "> Generated by `scripts/lean_execution_process.py`; do not hand-edit.",
        "",
        "This is synthetic process-control evidence only. It executes no Lean, CTest,",
        "`lean4export`, Axeyum, or U2 case and grants zero parity credit.",
        "",
        "## Summary",
        "",
        f"- Registered/retained controls: **{summary['registered_controls']}/{summary['retained_process_attempts']}**",
        f"- Retained files/bytes: **{summary['retained_files']} / {summary['retained_bytes']}**",
        f"- Raw stdout/stderr artifacts: **{summary['raw_artifacts']}**",
        "- Case records / completion records: **0 / 0**",
        "- Official outcomes / Axeyum outcomes / paired cells: **0 / 0 / 0**",
        "- Terminal Lean parity credit: **0**",
        "",
        "## Controls",
        "",
        "| Control | Lane | Terminal | Exit | Signal | Wall ms | Peak RSS bytes | Cleanup |",
        "|---|---|---|---:|---:|---:|---:|---|",
    ]
    for row in authority["controls"]:
        wall = row["wall_time"]["value"]
        rss = row["peak_rss"]["value"]
        cleanup = (
            "reaped/no-live-members"
            if row["direct_child_reaped"] and row["live_non_zombie_pids_after_cleanup"] == []
            else "no-child"
        )
        lines.append(
            f"| `{row['control_id']}` | `{row['lane_id']}` | `{row['observed_terminal_class']}` | "
            f"{row['exit_code'] if row['exit_code'] is not None else '—'} | "
            f"{row['signal'] if row['signal'] is not None else '—'} | "
            f"{wall if wall is not None else 'not-observed'} | "
            f"{rss if rss is not None else 'not-observed'} | {cleanup} |"
        )
    lines.extend(
        [
            "",
            "CPU time is deliberately `not-observed`: TL0.7.2 does not present a",
            "cumulative `RUSAGE_CHILDREN` delta as isolated per-attempt evidence. Peak RSS",
            "is the sampled root-process Linux `VmHWM`/`VmRSS`, not aggregate-tree memory.",
            "",
            "## Residual",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in authority["residual"])
    return "\n".join(lines) + "\n"


def generate_result(
    *,
    evidence_root: Path,
    implementation_revision: str | None,
    check: bool,
) -> None:
    if check:
        try:
            committed = json.loads(RESULT_AUTHORITY.read_bytes())
        except (OSError, json.JSONDecodeError) as exc:
            raise ProcessEvidenceError("cannot read committed result authority") from exc
        failures = validate_result_authority(committed)
        if failures:
            raise ProcessEvidenceError("; ".join(failures))
        authority = committed
    else:
        if implementation_revision is None:
            raise ProcessEvidenceError("generation requires --implementation-revision")
        authority = build_result_authority(
            evidence_root, implementation_revision=implementation_revision
        )
    summary = build_result_summary(authority)
    outputs = {
        RESULT_AUTHORITY: json.dumps(authority, indent=2) + "\n",
        RESULT_JSON: json.dumps(summary, indent=2) + "\n",
        RESULT_MARKDOWN: render_result_markdown(authority),
    }
    if check:
        stale = [path for path, content in outputs.items() if not path.is_file() or path.read_text() != content]
        if stale:
            raise ProcessEvidenceError(
                "stale generated result: " + ", ".join(path.relative_to(ROOT).as_posix() for path in stale)
            )
    else:
        for path, content in outputs.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print(
        "LEAN_PROCESS_RESULT|"
        f"controls={summary['summary']['retained_process_attempts']}|"
        f"files={summary['summary']['retained_files']}|"
        "real_outcomes=0|paired_cells=0|parity_credit=0"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command_name", required=True)
    write_parser = subparsers.add_parser("write-spec")
    write_parser.add_argument("--control", choices=CONTROL_IDS, required=True)
    write_parser.add_argument("--output", type=Path, required=True)
    run_parser = subparsers.add_parser("run-spec")
    run_parser.add_argument("--spec", type=Path, required=True)
    run_parser.add_argument("--output-dir", type=Path, required=True)
    validate_parser = subparsers.add_parser("validate-attempt")
    validate_parser.add_argument("--control", choices=CONTROL_IDS, required=True)
    validate_parser.add_argument("--directory", type=Path, required=True)
    result_parser = subparsers.add_parser("result")
    result_parser.add_argument(
        "--evidence-root",
        type=Path,
        default=ROOT / "docs/plan/evidence/lean-execution-process-tl0.7.2",
    )
    result_parser.add_argument("--implementation-revision")
    result_parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        if args.command_name == "write-spec":
            write_control_spec(args.control, args.output)
        elif args.command_name == "run-spec":
            terminal = execute_spec(read_canonical_spec(args.spec), args.output_dir)
            print(
                "LEAN_PROCESS_ATTEMPT|"
                f"control={terminal['attempt_id'].removeprefix('attempt-')}|"
                f"class={terminal['terminal']['class']}|credit=zero"
            )
        elif args.command_name == "validate-attempt":
            failures = validate_attempt_directory(
                args.directory, expected_spec=build_control_spec(args.control)
            )
            if failures:
                raise ProcessEvidenceError("; ".join(failures))
            print(f"LEAN_PROCESS_ATTEMPT_VALID|control={args.control}|credit=zero")
        elif args.command_name == "result":
            generate_result(
                evidence_root=args.evidence_root,
                implementation_revision=args.implementation_revision,
                check=args.check,
            )
        else:  # pragma: no cover
            raise AssertionError(args.command_name)
    except ProcessEvidenceError as exc:
        print(f"LEAN_PROCESS_ATTEMPT_ERROR|{exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
