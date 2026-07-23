#!/usr/bin/env python3
"""Qualify and run the source-first M2 R5 32 GiB attempt-003 lane."""

from __future__ import annotations

import argparse
import os
import resource
import signal
import subprocess
import sys
import tempfile
import time
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Callable, Iterator

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import lean_u2_official_execution as BASE  # noqa: E402
from scripts import lean_u2_official_execution_m2 as M2  # noqa: E402
from scripts import lean_u2_official_execution_m2_r3 as R3  # noqa: E402
from scripts import lean_u2_official_execution_m2_r4 as R4  # noqa: E402
from scripts import lean_u2_official_execution_m2_run as OLD_RUN  # noqa: E402


PLAN = ROOT / (
    "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r5-"
    "attempt-003-plan-2026-07-23.md"
)
PREREGISTRATION_COMMIT = "107ee5522e3a29bc70258c82d75aa12601a1082f"
PLAN_SHA256 = "12fc9fc218f31a105b09634da875ccebd653bcb92bde96ad605cc057297d6b82"
R4_RESULT = ROOT / (
    "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r4-"
    "control-result-2026-07-23.md"
)
R4_RESULT_SHA256 = "ced2d1d4d747dd564e703cc2a1aa58c7ccc21aa32c73a9902c96f8f37de27c07"

RUN_ID = "tl0.6.3-m2-release-linux-shard-0001-v4"
ATTEMPT_ID = "attempt-003"
SEQUENCE = 3
LANE_ID = "official-ctest-local-32g-lean-j1-stack512m-shard64-v4"
MEMORY_LIMIT_BYTES = 34_359_738_368
STACK_SIZE_KB = R4.STACK_SIZE_KB
STACK_SIZE_BYTES = R4.STACK_SIZE_BYTES
STACK_ENV = R4.STACK_ENV

DEFAULT_SOURCE_REPO = R4.DEFAULT_SOURCE_REPO
DEFAULT_TOOLCHAIN_ROOT = R4.DEFAULT_TOOLCHAIN_ROOT
DEFAULT_EVIDENCE_ROOT = ROOT / (
    "docs/plan/evidence/"
    "lean-u2-official-execution-tl0.6.3-m2-shard-0001-r5-attempt-003"
)
CONTROL_ROOT_PREFIX = "/home/mjbommar/.cache/axeyum-tl063-m2-r5-control-"
WORK_ROOT_PREFIX = "/home/mjbommar/.cache/axeyum-tl063-m2-r5-"

COMPLETION_SCHEMA = "axeyum-lean-u2-official-execution-m2-r5-completion-v1"
RECORD_SET_DOMAIN = "axeyum-lean-u2-official-execution-m2-r5-record-set-v1"
FULL_DOMAIN = "axeyum-lean-u2-official-execution-m2-r5-generated-files-v1"
RETAINED_DOMAIN = "axeyum-lean-u2-official-execution-m2-r5-retained-files-v1"
METADATA_DOMAIN = "axeyum-lean-u2-official-execution-m2-r5-metadata-files-v1"
ALLOWED_DOMAIN = "axeyum-lean-u2-official-execution-m2-r5-allowed-paths-v1"

CONTROL_SPEC_SCHEMA = "axeyum-lean-u2-official-execution-m2-r5-control-spec-v1"
CONTROL_PRELAUNCH_SCHEMA = (
    "axeyum-lean-u2-official-execution-m2-r5-control-prelaunch-v1"
)
CONTROL_TERMINAL_SCHEMA = (
    "axeyum-lean-u2-official-execution-m2-r5-control-terminal-v1"
)
CONTROL_COMPLETION_SCHEMA = (
    "axeyum-lean-u2-official-execution-m2-r5-control-completion-v1"
)
CONTROL_RECORD_SET_DOMAIN = (
    "axeyum-lean-u2-official-execution-m2-r5-control-record-set-v1"
)
CONTROL_TIMEOUT_MS = 120_000
CONTROL_GRACE_MS = 1_000
CONTROL_SOURCE = R4.FANOUT_SOURCE
CONTROL_SOURCE_SHA256 = R4.BASE.sha256_bytes(CONTROL_SOURCE)
CONTROL_SUCCESS = R4.FANOUT_SUCCESS
CONTROL_FIXED_PATHS = (
    "host.json",
    "prelaunch.json",
    "raw/stderr.bin",
    "raw/stdout.bin",
    "source/probe.lean",
    "spec.json",
    "terminal.json",
)

_R4_BUILD_SPEC = R4.build_spec
_R4_RESOURCE_ENVELOPE = R4.resource_envelope


class R5Error(ValueError):
    """The R5 preregistration, control, execution, or evidence drifted."""


def validate_history() -> dict[str, Any]:
    history = R4.validate_history()
    if (
        not M2.HEX40.fullmatch(PREREGISTRATION_COMMIT)
        or not PLAN.is_file()
        or BASE.sha256_file(PLAN) != PLAN_SHA256
        or not R4_RESULT.is_file()
        or BASE.sha256_file(R4_RESULT) != R4_RESULT_SHA256
        or R4.DEFAULT_EVIDENCE_ROOT.exists()
        or Path(R4.WORK_ROOT_PREFIX + "628c5911").exists()
    ):
        raise R5Error("R5 preregistration, R4 result, or selected-root history drift")
    return history


def resource_envelope() -> dict[str, Any]:
    envelope = dict(_R4_RESOURCE_ENVELOPE())
    envelope.update(
        {
            "lane_id": LANE_ID,
            "memory_limit": BASE.metric("observed", MEMORY_LIMIT_BYTES, "bytes"),
        }
    )
    return envelope


def build_spec(**kwargs: Any) -> dict[str, Any]:
    spec = _R4_BUILD_SPEC(**kwargs)
    spec.update(
        {
            "preregistration_commit": PREREGISTRATION_COMMIT,
            "plan_sha256": PLAN_SHA256,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "sequence": SEQUENCE,
            "resource_envelope": resource_envelope(),
        }
    )
    spec["prior_history"].update(
        {
            "r4_control_result_sha256": R4_RESULT_SHA256,
            "r4_selected_processes": 0,
            "selected_attempt_unconsumed": True,
        }
    )
    spec["record_sha256"] = ""
    return BASE.seal(spec, M2.SPEC_SCHEMA)


def validate_spec(spec: Any) -> list[str]:
    if not isinstance(spec, dict) or not BASE.valid_seal(spec, M2.SPEC_SCHEMA):
        return ["R5 spec identity drift"]
    try:
        expected = build_spec(
            implementation_revision=spec["implementation_revision"],
            source_root=Path(spec["source_root"]),
            toolchain_root=Path(spec["toolchain_root"]),
            harness_build=Path(spec["harness_build"]),
            junit_path=Path(spec["junit_path"]),
        )
    except (KeyError, TypeError, R4.R4Error, R5Error) as error:
        return [f"R5 spec cannot be reconstructed: {error}"]
    return [] if spec == expected else ["R5 spec field or linkage drift"]


@contextmanager
def r5_bindings() -> Iterator[None]:
    m2 = {
        "RUN_ID": RUN_ID,
        "ATTEMPT_ID": ATTEMPT_ID,
        "SEQUENCE": SEQUENCE,
        "LANE_ID": LANE_ID,
        "MEMORY_LIMIT_BYTES": MEMORY_LIMIT_BYTES,
        "resource_envelope": resource_envelope,
        "build_spec": build_spec,
        "validate_spec": validate_spec,
        "render_environment_wrapper": R4.render_environment_wrapper,
        "build_harness_record": R4.build_harness_record,
        "case_generated_paths": R3.case_generated_paths,
        "declared_generated_paths": R3.declared_generated_paths,
        "build_post_record": R4.build_post_record,
        "result_projection": R4.result_projection,
    }
    shared = {
        "PREREGISTRATION_COMMIT": PREREGISTRATION_COMMIT,
        "PLAN_SHA256": PLAN_SHA256,
        "RUN_ID": RUN_ID,
        "ATTEMPT_ID": ATTEMPT_ID,
        "SEQUENCE": SEQUENCE,
        "LANE_ID": LANE_ID,
        "DEFAULT_EVIDENCE_ROOT": DEFAULT_EVIDENCE_ROOT,
        "WORK_ROOT_PREFIX": WORK_ROOT_PREFIX,
        "COMPLETION_SCHEMA": COMPLETION_SCHEMA,
        "RECORD_SET_DOMAIN": RECORD_SET_DOMAIN,
        "FULL_DOMAIN": FULL_DOMAIN,
        "RETAINED_DOMAIN": RETAINED_DOMAIN,
        "METADATA_DOMAIN": METADATA_DOMAIN,
        "ALLOWED_DOMAIN": ALLOWED_DOMAIN,
        "resource_envelope": resource_envelope,
        "build_spec": build_spec,
        "validate_spec": validate_spec,
    }
    previous_m2 = {name: getattr(M2, name) for name in m2}
    previous_r3 = {name: getattr(R3, name) for name in shared}
    previous_r4 = {
        name: getattr(R4, name) for name in shared if hasattr(R4, name)
    }
    try:
        for name, value in m2.items():
            setattr(M2, name, value)
        for module in (R3, R4):
            for name, value in shared.items():
                if hasattr(module, name):
                    setattr(module, name, value)
        yield
    finally:
        for name, value in previous_r4.items():
            setattr(R4, name, value)
        for name, value in previous_r3.items():
            setattr(R3, name, value)
        for name, value in previous_m2.items():
            setattr(M2, name, value)


def _host_record() -> dict[str, Any]:
    meminfo: dict[str, int] = {}
    for line in Path("/proc/meminfo").read_text(encoding="ascii").splitlines():
        key, value = line.split(":", 1)
        fields = value.split()
        if key in {
            "MemAvailable",
            "CommitLimit",
            "Committed_AS",
            "SwapTotal",
            "SwapFree",
        }:
            meminfo[key] = int(fields[0]) * 1024
    return BASE.seal(
        {
            "schema": "axeyum-lean-u2-official-execution-m2-r5-control-host-v1",
            "meminfo_bytes": meminfo,
            "overcommit_memory": int(
                Path("/proc/sys/vm/overcommit_memory").read_text().strip()
            ),
            "pid_limit": resource.getrlimit(resource.RLIMIT_NPROC)[0],
            "official_provider_claimed": False,
            "performance_credit": False,
            "record_sha256": "",
        },
        "axeyum-lean-u2-official-execution-m2-r5-control-host-v1",
    )


def _sample_process(pid: int) -> dict[str, int] | None:
    try:
        values: dict[str, int] = {}
        for line in Path(f"/proc/{pid}/status").read_text().splitlines():
            key, value = line.split(":", 1)
            if key in {"VmPeak", "VmSize", "VmRSS"}:
                values[key] = int(value.split()[0]) * 1024
            elif key == "Threads":
                values[key] = int(value.strip())
        return values if set(values) == {"VmPeak", "VmSize", "VmRSS", "Threads"} else None
    except (FileNotFoundError, ProcessLookupError, ValueError):
        return None


def _control_spec(
    *, implementation_revision: str, control_root: Path, toolchain_root: Path
) -> dict[str, Any]:
    source = control_root / "source/probe.lean"
    lean = toolchain_root.resolve() / "bin/lean"
    environment = {
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        STACK_ENV: str(STACK_SIZE_KB),
        "PATH": f"{toolchain_root.resolve() / 'bin'}:/usr/bin:/bin",
        "TZ": "UTC",
    }
    return BASE.seal(
        {
            "schema": CONTROL_SPEC_SCHEMA,
            "implementation_revision": implementation_revision,
            "preregistration_commit": PREREGISTRATION_COMMIT,
            "plan_sha256": PLAN_SHA256,
            "control_id": "released-lean-nine-dedicated-tasks-32g-v1",
            "selected_attempt_id": ATTEMPT_ID,
            "selected_attempt_consumed": False,
            "assigned_case_ids": [],
            "command": [str(lean), "--run", str(source)],
            "lean_sha256": BASE.PINNED_LEAN_SHA256,
            "working_directory": str(control_root),
            "environment": environment,
            "memory_limit_bytes": MEMORY_LIMIT_BYTES,
            "wall_timeout_ms": CONTROL_TIMEOUT_MS,
            "terminate_grace_ms": CONTROL_GRACE_MS,
            "source": {
                "path": "source/probe.lean",
                "bytes": len(CONTROL_SOURCE),
                "sha256": CONTROL_SOURCE_SHA256,
            },
            "expected_stdout_sha256": BASE.sha256_bytes(CONTROL_SUCCESS),
            "expected_stderr_sha256": BASE.sha256_bytes(b""),
            "credits": dict(M2.ZERO_TERMINAL_CREDITS),
            "record_sha256": "",
        },
        CONTROL_SPEC_SCHEMA,
    )


def _control_inventory(root: Path) -> list[dict[str, Any]]:
    return [row for row in BASE.manifest_tree(root) if row["path"] != "completion.json"]


def run_control(
    *,
    implementation_revision: str,
    control_root: Path,
    toolchain_root: Path,
    popen_factory: Callable[..., subprocess.Popen[bytes]] = subprocess.Popen,
    live_members: Callable[[int], list[int]] = BASE.PROCESS._live_process_group_members,
    sample_process: Callable[[int], dict[str, int] | None] = _sample_process,
) -> dict[str, Any]:
    validate_history()
    validate_revision_preflight(implementation_revision)
    expected_root = Path(CONTROL_ROOT_PREFIX + implementation_revision[:8])
    if control_root.resolve() != expected_root or control_root.exists() or control_root.is_symlink():
        raise R5Error("R5 control root must be the new frozen revision-named path")
    toolchain = toolchain_root.resolve()
    lean = toolchain / "bin/lean"
    if (
        not lean.is_file()
        or lean.is_symlink()
        or BASE.sha256_file(lean) != BASE.PINNED_LEAN_SHA256
    ):
        raise R5Error("R5 control lacks regular released Lean")
    control_root.mkdir(parents=True, mode=0o700)
    spec = _control_spec(
        implementation_revision=implementation_revision,
        control_root=control_root,
        toolchain_root=toolchain,
    )
    prelaunch = BASE.seal(
        {
            "schema": CONTROL_PRELAUNCH_SCHEMA,
            "spec_sha256": spec["record_sha256"],
            "recorded_before_launch": True,
            "selected_attempt_consumed": False,
            "record_sha256": "",
        },
        CONTROL_PRELAUNCH_SCHEMA,
    )
    BASE.install_bytes(control_root, "source/probe.lean", CONTROL_SOURCE)
    BASE.install_json(control_root, "host.json", _host_record())
    BASE.install_json(control_root, "spec.json", spec)
    BASE.install_json(control_root, "prelaunch.json", prelaunch)
    samples: list[dict[str, int]] = []
    events = ["prelaunch-installed"]
    watchdog = False
    sigterm_sent = False
    sigkill_sent = False
    reaped = False
    live: list[int] = []
    started = time.monotonic_ns()
    with tempfile.TemporaryDirectory(prefix="axeyum-m2-r5-control-private-") as temp:
        stdout_path = Path(temp) / "stdout.bin"
        stderr_path = Path(temp) / "stderr.bin"
        with stdout_path.open("xb", buffering=0) as stdout_handle, stderr_path.open(
            "xb", buffering=0
        ) as stderr_handle:
            process = popen_factory(
                spec["command"],
                cwd=spec["working_directory"],
                env=spec["environment"],
                stdin=subprocess.DEVNULL,
                stdout=stdout_handle,
                stderr=stderr_handle,
                shell=False,
                close_fds=True,
                start_new_session=True,
                preexec_fn=BASE.PROCESS._limit_hook(MEMORY_LIMIT_BYTES),
            )
            events.append("rlimit-as-installed")
            sample = sample_process(process.pid)
            if sample is not None:
                samples.append(sample)
            deadline = started + CONTROL_TIMEOUT_MS * 1_000_000
            while process.poll() is None and time.monotonic_ns() < deadline:
                sample = sample_process(process.pid)
                if sample is not None and (not samples or sample != samples[-1]):
                    samples.append(sample)
                time.sleep(0.01)
            if process.poll() is None:
                watchdog = True
                events.append("wall-timeout-observed")
                try:
                    os.killpg(process.pid, signal.SIGTERM)
                    sigterm_sent = True
                    events.append("process-group-sigterm-sent")
                except ProcessLookupError:
                    pass
                grace = time.monotonic_ns() + CONTROL_GRACE_MS * 1_000_000
                while time.monotonic_ns() < grace and live_members(process.pid):
                    time.sleep(0.01)
                if live_members(process.pid):
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                        sigkill_sent = True
                        events.append("process-group-sigkill-sent")
                    except ProcessLookupError:
                        pass
            try:
                process.wait(timeout=3)
                reaped = True
                events.append("direct-child-reaped")
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                sigkill_sent = True
                process.wait(timeout=3)
                reaped = True
                events.append("direct-child-reaped")
            live = live_members(process.pid)
            cleanup_deadline = time.monotonic_ns() + 1_000_000_000
            while live and time.monotonic_ns() < cleanup_deadline:
                time.sleep(0.01)
                live = live_members(process.pid)
            if not live:
                events.append("process-group-no-live-members-observed")
        stdout = stdout_path.read_bytes()
        stderr = stderr_path.read_bytes()
    elapsed = max(1, (time.monotonic_ns() - started) // 1_000_000)
    code = process.returncode
    terminal_class = (
        "wall-timeout" if watchdog else "signaled" if code < 0 else "exited"
    )
    terminal = BASE.seal(
        {
            "schema": CONTROL_TERMINAL_SCHEMA,
            "spec_sha256": spec["record_sha256"],
            "prelaunch_sha256": prelaunch["record_sha256"],
            "class": terminal_class,
            "exit_code": code if code >= 0 else None,
            "signal": -code if code < 0 else None,
            "events": events,
            "wall_time": BASE.metric("observed", elapsed, "milliseconds"),
            "memory_limit": BASE.metric("observed", MEMORY_LIMIT_BYTES, "bytes"),
            "samples": samples,
            "process": {
                "pid": process.pid,
                "watchdog_fired": watchdog,
                "sigterm_sent": sigterm_sent,
                "sigkill_sent": sigkill_sent,
                "direct_child_reaped": reaped,
                "live_non_zombie_pids_after_cleanup": live,
            },
            "raw_outputs": [
                {
                    "path": "raw/stderr.bin",
                    "bytes": len(stderr),
                    "sha256": BASE.sha256_bytes(stderr),
                },
                {
                    "path": "raw/stdout.bin",
                    "bytes": len(stdout),
                    "sha256": BASE.sha256_bytes(stdout),
                },
            ],
            "authorized_selected_execution": (
                terminal_class == "exited"
                and code == 0
                and stdout == CONTROL_SUCCESS
                and stderr == b""
                and reaped
                and live == []
            ),
            "selected_attempt_consumed": False,
            "credits": dict(M2.ZERO_TERMINAL_CREDITS),
            "record_sha256": "",
        },
        CONTROL_TERMINAL_SCHEMA,
    )
    BASE.install_bytes(control_root, "raw/stdout.bin", stdout)
    BASE.install_bytes(control_root, "raw/stderr.bin", stderr)
    BASE.install_json(control_root, "terminal.json", terminal)
    dependencies = _control_inventory(control_root)
    completion = BASE.seal(
        {
            "schema": CONTROL_COMPLETION_SCHEMA,
            "state": "complete-control-evidence",
            "completion_installed_last": True,
            "dependencies": dependencies,
            "record_set_sha256": BASE.domain_digest(
                CONTROL_RECORD_SET_DOMAIN, dependencies
            ),
            "terminal_sha256": terminal["record_sha256"],
            "authorized_selected_execution": terminal[
                "authorized_selected_execution"
            ],
            "selected_attempt_consumed": False,
            "credits": dict(M2.ZERO_TERMINAL_CREDITS),
            "record_sha256": "",
        },
        CONTROL_COMPLETION_SCHEMA,
    )
    BASE.install_json(control_root, "completion.json", completion)
    validate_control(control_root, require_authorized=False)
    return completion


def validate_control(root: Path, *, require_authorized: bool) -> dict[str, Any]:
    expected = {*CONTROL_FIXED_PATHS, "completion.json"}
    present = {row["path"] for row in BASE.manifest_tree(root)}
    if present != expected:
        raise R5Error("R5 control namespace drift")
    source = (root / "source/probe.lean").read_bytes()
    spec = BASE.load_canonical(root / "spec.json")
    prelaunch = BASE.load_canonical(root / "prelaunch.json")
    terminal = BASE.load_canonical(root / "terminal.json")
    completion = BASE.load_canonical(root / "completion.json")
    stdout = (root / "raw/stdout.bin").read_bytes()
    stderr = (root / "raw/stderr.bin").read_bytes()
    if (
        source != CONTROL_SOURCE
        or not BASE.valid_seal(spec, CONTROL_SPEC_SCHEMA)
        or spec != _control_spec(
            implementation_revision=spec["implementation_revision"],
            control_root=root,
            toolchain_root=Path(spec["command"][0]).parents[1],
        )
        or not BASE.valid_seal(prelaunch, CONTROL_PRELAUNCH_SCHEMA)
        or prelaunch["spec_sha256"] != spec["record_sha256"]
        or not BASE.valid_seal(terminal, CONTROL_TERMINAL_SCHEMA)
        or terminal["spec_sha256"] != spec["record_sha256"]
        or terminal["prelaunch_sha256"] != prelaunch["record_sha256"]
        or terminal["raw_outputs"]
        != [
            {
                "path": "raw/stderr.bin",
                "bytes": len(stderr),
                "sha256": BASE.sha256_bytes(stderr),
            },
            {
                "path": "raw/stdout.bin",
                "bytes": len(stdout),
                "sha256": BASE.sha256_bytes(stdout),
            },
        ]
        or terminal["selected_attempt_consumed"] is not False
        or any(terminal["credits"].values())
    ):
        raise R5Error("R5 control source, record, raw, or credit drift")
    dependencies = _control_inventory(root)
    expected_completion = BASE.seal(
        {
            "schema": CONTROL_COMPLETION_SCHEMA,
            "state": "complete-control-evidence",
            "completion_installed_last": True,
            "dependencies": dependencies,
            "record_set_sha256": BASE.domain_digest(
                CONTROL_RECORD_SET_DOMAIN, dependencies
            ),
            "terminal_sha256": terminal["record_sha256"],
            "authorized_selected_execution": terminal[
                "authorized_selected_execution"
            ],
            "selected_attempt_consumed": False,
            "credits": dict(M2.ZERO_TERMINAL_CREDITS),
            "record_sha256": "",
        },
        CONTROL_COMPLETION_SCHEMA,
    )
    if completion != expected_completion:
        raise R5Error("R5 control completion or dependency drift")
    if require_authorized and (
        not completion["authorized_selected_execution"]
        or terminal["class"] != "exited"
        or terminal["exit_code"] != 0
        or stdout != CONTROL_SUCCESS
        or stderr != b""
        or not terminal["process"]["direct_child_reaped"]
        or terminal["process"]["live_non_zombie_pids_after_cleanup"] != []
    ):
        raise R5Error("R5 control does not authorize selected execution")
    BASE.validate_live_readonly_tree(root)
    return completion


def validate_complete_evidence(root: Path) -> dict[str, Any]:
    validate_history()
    with r5_bindings():
        return R3.validate_complete_evidence(root)


def validate_offline_contract() -> dict[str, Any]:
    validate_history()
    spec = build_spec(
        implementation_revision="0" * 40,
        source_root=Path("/r5/source"),
        toolchain_root=Path("/r5/toolchain"),
        harness_build=Path("/r5/harness"),
        junit_path=Path("/r5/attempt/test-results.xml"),
    )
    if validate_spec(spec):
        raise R5Error("R5 offline spec drift")
    r4 = R4.resource_envelope()
    r5 = resource_envelope()
    normalized = dict(r4)
    normalized.update({"lane_id": r5["lane_id"], "memory_limit": r5["memory_limit"]})
    if normalized != r5 or len(M2.selected_contract()["cases"]) != 64:
        raise R5Error("R5 resource-only delta or shard drift")
    return {
        "cases": 64,
        "generated": len(R3.declared_generated_paths()),
        "memory_limit_bytes": MEMORY_LIMIT_BYTES,
        "selected_processes": 0,
        "controls": 0,
        "outcomes": 0,
        "parity": 0,
    }


def validate_revision_preflight(revision: str) -> None:
    OLD_RUN.validate_revision_preflight(revision)
    branch = OLD_RUN._git(ROOT, "branch", "--show-current")
    remote = OLD_RUN._git(ROOT, "ls-remote", "--heads", "origin", branch).split()
    if len(remote) != 2 or remote[0] != revision:
        raise R5Error("R5 implementation revision is not remote-equal")


def validate_live_paths(args: argparse.Namespace) -> None:
    if args.work_root.resolve() != Path(WORK_ROOT_PREFIX + args.implementation_revision[:8]):
        raise R5Error("R5 selected work root substitution")
    if args.evidence_root.resolve() != DEFAULT_EVIDENCE_ROOT.resolve():
        raise R5Error("R5 evidence root substitution")
    if args.source_repo.resolve() != DEFAULT_SOURCE_REPO.resolve():
        raise R5Error("R5 source repository substitution")
    if args.toolchain_root.resolve() != DEFAULT_TOOLCHAIN_ROOT.resolve():
        raise R5Error("R5 toolchain substitution")


def run_r5(args: argparse.Namespace) -> None:
    validate_offline_contract()
    validate_revision_preflight(args.implementation_revision)
    validate_live_paths(args)
    completion = validate_control(args.control_root, require_authorized=True)
    if completion["record_sha256"] != args.control_completion_sha256:
        raise R5Error("R5 explicit control completion digest mismatch")

    def cached_control(_toolchain_root: Path) -> dict[str, Any]:
        terminal = BASE.load_canonical(args.control_root / "terminal.json")
        return {"record_sha256": terminal["record_sha256"]}

    bindings: dict[str, Any] = {
        "validate_offline_contract": validate_offline_contract,
        "validate_revision_preflight": validate_revision_preflight,
        "validate_live_paths": validate_live_paths,
        "probe_fanout": cached_control,
        "r4_bindings": r5_bindings,
        "validate_complete_evidence": validate_complete_evidence,
        "RUN_ID": RUN_ID,
        "ATTEMPT_ID": ATTEMPT_ID,
        "SEQUENCE": SEQUENCE,
        "LANE_ID": LANE_ID,
        "MEMORY_LIMIT_BYTES": MEMORY_LIMIT_BYTES,
        "DEFAULT_EVIDENCE_ROOT": DEFAULT_EVIDENCE_ROOT,
        "WORK_ROOT_PREFIX": WORK_ROOT_PREFIX,
    }
    previous = {name: getattr(R4, name) for name in bindings}
    try:
        for name, value in bindings.items():
            setattr(R4, name, value)
        args.fanout_record_sha256 = BASE.load_canonical(
            args.control_root / "terminal.json"
        )["record_sha256"]
        R4.run_r4(args)
    finally:
        for name, value in previous.items():
            setattr(R4, name, value)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("offline-check")
    stack = commands.add_parser("probe-stack")
    stack.add_argument("--toolchain-root", type=Path, default=DEFAULT_TOOLCHAIN_ROOT)
    control = commands.add_parser("run-control")
    control.add_argument("--implementation-revision", required=True)
    control.add_argument("--control-root", type=Path, required=True)
    control.add_argument("--toolchain-root", type=Path, default=DEFAULT_TOOLCHAIN_ROOT)
    validate_control_cmd = commands.add_parser("validate-control")
    validate_control_cmd.add_argument("--control-root", type=Path, required=True)
    validate_control_cmd.add_argument("--require-authorized", action="store_true")
    run = commands.add_parser("run-r5")
    run.add_argument("--implementation-revision", required=True)
    run.add_argument("--control-root", type=Path, required=True)
    run.add_argument("--control-completion-sha256", required=True)
    run.add_argument("--source-repo", type=Path, default=DEFAULT_SOURCE_REPO)
    run.add_argument("--toolchain-root", type=Path, default=DEFAULT_TOOLCHAIN_ROOT)
    run.add_argument("--work-root", type=Path, required=True)
    run.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    validate = commands.add_parser("validate")
    validate.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    args = parser.parse_args()
    try:
        if args.command == "offline-check":
            summary = validate_offline_contract()
            print(
                "LEAN_U2_M2_R5|"
                f"cases={summary['cases']}|generated={summary['generated']}|"
                f"memory={MEMORY_LIMIT_BYTES}|controls=0|selected_processes=0|"
                "outcomes=0|pairs=0|parity=0"
            )
        elif args.command == "probe-stack":
            result = R4.probe_stack_environment(args.toolchain_root)
            print(
                "LEAN_U2_M2_R5_STACK_PROBE|"
                f"source={result['source_sha256']}|exit=0|value={STACK_SIZE_KB}|"
                "selected_case=false"
            )
        elif args.command == "run-control":
            result = run_control(
                implementation_revision=args.implementation_revision,
                control_root=args.control_root,
                toolchain_root=args.toolchain_root,
            )
            state = "AUTHORIZED" if result["authorized_selected_execution"] else "BLOCKED"
            print(
                f"LEAN_U2_M2_R5_CONTROL_{state}|"
                f"completion={result['record_sha256']}|selected_attempt_consumed=false|"
                "outcomes=0|parity=0"
            )
            if not result["authorized_selected_execution"]:
                return 1
        elif args.command == "validate-control":
            result = validate_control(
                args.control_root, require_authorized=args.require_authorized
            )
            print(
                "LEAN_U2_M2_R5_CONTROL_VALID|"
                f"completion={result['record_sha256']}|"
                f"authorized={str(result['authorized_selected_execution']).lower()}|"
                "selected_attempt_consumed=false|parity=0"
            )
        elif args.command == "run-r5":
            run_r5(args)
        elif args.command == "validate":
            result = validate_complete_evidence(args.evidence_root)
            print(
                "LEAN_U2_M2_R5_EVIDENCE_VALID|"
                f"completion={result['record_sha256']}|cases=64|parity=0"
            )
        else:  # pragma: no cover
            raise AssertionError(args.command)
    except (
        BASE.U2ExecutionError,
        BASE.STORE.CheckpointConflict,
        M2.M2ContractError,
        OLD_RUN.M2RunError,
        R3.R3Error,
        R4.R4Error,
        R5Error,
    ) as error:
        print(f"LEAN_U2_M2_R5_ERROR|{error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
