#!/usr/bin/env python3
"""Prepare, run once, retain, and validate the preregistered Lean U2 M2 shard."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path, PurePosixPath
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import lean_u2_official_execution as BASE  # noqa: E402
from scripts import lean_u2_official_execution_m2 as M2  # noqa: E402
from scripts import lean_u2_official_execution_m2_store as M2_STORE  # noqa: E402
from scripts import lean_u2_official_execution_r2 as R2  # noqa: E402


DEFAULT_EVIDENCE_ROOT = ROOT / (
    "docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m2-shard-0001"
)
PLATFORM_SCHEMA = "axeyum-lean-u2-official-execution-m2-platform-v1"
LANE_SCHEMA = "axeyum-lean-u2-official-execution-m2-lane-v1"
SHARD_SCHEMA = "axeyum-lean-u2-official-execution-m2-shard-v1"
DISCOVERY_SCHEMA = "axeyum-lean-u2-official-execution-m2-discovery-v1"
RUN_SCHEMA = "axeyum-lean-u2-official-execution-m2-run-v1"
PRELAUNCH_SCHEMA = "axeyum-lean-u2-official-execution-m2-prelaunch-v1"
TERMINAL_SCHEMA = "axeyum-lean-u2-official-execution-m2-terminal-v1"

R1_PLAN = ROOT / (
    "docs/plan/"
    "lean-u2-official-execution-tl0.6.3-m2-r1-symlink-preflight-plan-2026-07-22.md"
)
R1_PREREGISTRATION_COMMIT = "3e761588eb8487dab510906e6d5fc3c90cc08fef"
R1_PLAN_SHA256 = "e0fd948ee39e0f1808eec459a18766683d3781e602cc481c8fa10a70e9a0d5f9"

COMPILE_BENCH_RUNNER_PATH = "tests/compile_bench/run_test.sh"
COMPILE_BENCH_RUNNER_ROW = {
    "path": COMPILE_BENCH_RUNNER_PATH,
    "kind": "symlink",
    "mode": 0o777,
    "bytes": 22,
    "sha256": "674a6c537535d76d6f10d195c61ad8da8de97e903f2735326e4a927a7e0d3299",
    "target": "../compile/run_test.sh",
}
COMPILE_RUNNER_TARGET_PATH = "tests/compile/run_test.sh"
COMPILE_RUNNER_TARGET_ROW = {
    "path": COMPILE_RUNNER_TARGET_PATH,
    "kind": "file",
    "mode": 0o644,
    "bytes": 1_212,
    "sha256": "557fe4726ec23d812a0649c56def2c22daa89faeddc58b7e49b118f3ab123396",
    "target": None,
}


class M2RunError(ValueError):
    """The M2 one-shot runner failed a frozen preflight or evidence rule."""


def _git(repository: Path, *args: str) -> str:
    completed = subprocess.run(
        ["/usr/bin/git", "-C", str(repository), *args],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=30,
    )
    if completed.returncode != 0:
        raise M2RunError(
            "git command failed: "
            + completed.stderr.decode("utf-8", errors="replace").strip()
        )
    return completed.stdout.decode("utf-8", errors="strict").strip()


def validate_revision_preflight(implementation_revision: str) -> None:
    if not M2.HEX40.fullmatch(implementation_revision):
        raise M2RunError("M2 implementation revision must be a full Git hash")
    if _git(ROOT, "rev-parse", "HEAD") != implementation_revision:
        raise M2RunError("working revision differs from M2 implementation revision")
    if _git(ROOT, "rev-parse", "@{upstream}") != implementation_revision:
        raise M2RunError("M2 implementation revision is not at the tracking revision")
    if _git(ROOT, "status", "--porcelain=v1", "--untracked-files=all"):
        raise M2RunError("working tree must be clean before M2 execution")


def _resolve_manifest_link(link_path: str, target: Any) -> str | None:
    """Resolve one relative manifest link without consulting the filesystem."""
    if not isinstance(target, str) or not target:
        return None
    target_path = PurePosixPath(target)
    if target_path.is_absolute():
        return None
    parts = list(PurePosixPath(link_path).parent.parts)
    for part in target_path.parts:
        if part in {"", "."}:
            continue
        if part == "..":
            if not parts:
                return None
            parts.pop()
        else:
            parts.append(part)
    if not parts:
        return None
    return PurePosixPath(*parts).as_posix()


def _validate_selected_runner(
    runner: Any, by_path: dict[Any, dict[str, Any]]
) -> bool:
    prefix = "$LEAN_ROOT/"
    if not isinstance(runner, str) or not runner.startswith(prefix):
        return False
    runner_path = runner[len(prefix) :]
    row = by_path.get(runner_path, {})
    if runner_path == COMPILE_BENCH_RUNNER_PATH:
        resolved = _resolve_manifest_link(runner_path, row.get("target"))
        target_row = by_path.get(resolved, {}) if resolved is not None else {}
        return (
            row == COMPILE_BENCH_RUNNER_ROW
            and resolved == COMPILE_RUNNER_TARGET_PATH
            and target_row == COMPILE_RUNNER_TARGET_ROW
        )
    if row.get("kind") == "file":
        return True
    if row.get("kind") != "symlink":
        return False
    resolved = _resolve_manifest_link(runner_path, row.get("target"))
    target_row = by_path.get(resolved, {}) if resolved is not None else {}
    if target_row.get("kind") != "file":
        return False
    return True


def validate_selected_source(source: Any) -> list[str]:
    failures = BASE.validate_source_record(source)
    if not isinstance(source, dict):
        return [*failures, "M2 source record is not an object"]
    rows = source.get("files", [])
    by_path = {row.get("path"): row for row in rows if isinstance(row, dict)}
    for case in M2.selected_contract()["cases"]:
        source_row = by_path.get(case["source_path"], {})
        if (
            source_row.get("kind") != "file"
            or source_row.get("sha256") != case["source_sha256"]
        ):
            failures.append(f"M2 selected source drift: {case['id']}")
        for sidecar in case["sidecars"]:
            if by_path.get(sidecar, {}).get("kind") != "file":
                failures.append(f"M2 selected sidecar missing: {sidecar}")
        if case["expected_path"] is not None and case["expected_path"] not in case["sidecars"]:
            failures.append(f"M2 expected-output registration drift: {case['id']}")
        runner = case["registration"]["command"][2]
        if not _validate_selected_runner(runner, by_path):
            failures.append(f"M2 selected runner missing: {case['id']}")
    return failures


def capture_source(source_repo: Path, source_root: Path) -> dict[str, Any]:
    source = BASE.capture_source(source_repo, source_root)
    failures = validate_selected_source(source)
    if failures:
        raise M2RunError("; ".join(failures))
    return source


def capture_toolchain(toolchain_root: Path, work_root: Path) -> dict[str, Any]:
    if R2._CURRENT_WORK_ROOT is not None:
        raise M2RunError("R2 compiler-probe root is already configured")
    R2._CURRENT_WORK_ROOT = work_root
    try:
        toolchain = R2.capture_toolchain(toolchain_root)
    finally:
        R2._CURRENT_WORK_ROOT = None
    failures = R2.validate_toolchain_record(toolchain)
    if failures:
        raise M2RunError("; ".join(failures))
    return toolchain


def _descriptor(path: str, payload: bytes) -> dict[str, Any]:
    return {
        "path": path,
        "bytes": len(payload),
        "sha256": BASE.sha256_bytes(payload),
    }


def prepare_harness(
    *,
    source_root: Path,
    toolchain_root: Path,
    harness_root: Path,
    run_command: Callable[..., subprocess.CompletedProcess[bytes]] = subprocess.run,
) -> tuple[dict[str, Any], dict[str, Any], bytes, bytes, bytes]:
    source = source_root.resolve()
    toolchain = toolchain_root.resolve()
    harness = harness_root.resolve()
    if harness.exists() or harness.is_symlink():
        raise M2RunError("M2 harness destination must be new")
    harness.mkdir(parents=True, mode=0o755)
    wrapper = M2.render_environment_wrapper(source, toolchain)
    wrapper_path = source / "tests/with_stage1_test_env.sh"
    if wrapper_path.exists() or wrapper_path.is_symlink():
        raise M2RunError("M2 generated environment wrapper already exists")
    wrapper_path.write_bytes(wrapper)
    wrapper_path.chmod(0o755)
    ctest = M2.render_ctest_file(
        source_root=source,
        toolchain_root=toolchain,
        harness_root=harness,
    )
    (harness / "CTestTestfile.cmake").write_bytes(ctest)
    command = [
        "/usr/bin/ctest",
        "--test-dir",
        str(harness),
        "--show-only=json-v1",
        "-E",
        "foreign",
    ]
    completed = run_command(
        command,
        cwd=source,
        env={
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "PATH": "/usr/bin:/bin",
            "TZ": "UTC",
        },
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=120,
    )
    if completed.returncode != 0:
        raise M2RunError(
            "M2 CTest discovery failed: "
            + completed.stderr.decode("utf-8", errors="replace").strip()
        )
    try:
        payload = json.loads(completed.stdout)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise M2RunError("M2 CTest discovery output is not JSON") from error
    try:
        normalized = M2.normalize_discovery(
            payload,
            source_root=source,
            toolchain_root=toolchain,
            harness_root=harness,
        )
        harness_record = M2.build_harness_record(
            source_root=source,
            toolchain_root=toolchain,
            harness_root=harness,
            discovery_payload=payload,
        )
    except M2.M2ContractError as error:
        raise M2RunError(str(error)) from error
    discovery = BASE.seal(
        {
            "schema": DISCOVERY_SCHEMA,
            "command": command,
            "raw": _descriptor("raw/discovery.json", completed.stdout),
            "normalized": normalized,
            "normalized_sha256": BASE.domain_digest(
                "axeyum-lean-u2-official-execution-m2-discovery-v1", normalized
            ),
            "record_sha256": "",
        },
        DISCOVERY_SCHEMA,
    )
    return harness_record, discovery, wrapper, ctest, completed.stdout


def build_platform_record(working_directory: Path) -> dict[str, Any]:
    platform = BASE.PROCESS.capture_platform(working_directory)
    libc = subprocess.run(
        ["/usr/bin/getconf", "GNU_LIBC_VERSION"],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=30,
    )
    return BASE.seal(
        {
            "schema": PLATFORM_SCHEMA,
            "captured_utc": dt.datetime.now(dt.UTC).isoformat().replace("+00:00", "Z"),
            "platform": platform,
            "uname": list(os.uname()),
            "glibc": (
                libc.stdout.decode("utf-8", errors="strict").strip()
                if libc.returncode == 0
                else "not-observed"
            ),
            "online_cpu_count": os.cpu_count(),
            "official_provider_claimed": False,
            "record_sha256": "",
        },
        PLATFORM_SCHEMA,
    )


def build_lane_record() -> dict[str, Any]:
    return BASE.seal(
        {
            "schema": LANE_SCHEMA,
            "lane_id": M2.LANE_ID,
            "resource_envelope": M2.resource_envelope(),
            "command_workers": 1,
            "lean_shell_workers": 1,
            "lean_num_threads": 1,
            "compiler_override": None,
            "task_stack_override": None,
            "official_provider_claimed": False,
            "performance_credit": False,
            "record_sha256": "",
        },
        LANE_SCHEMA,
    )


def build_shard_record() -> dict[str, Any]:
    contract = M2.selected_contract()
    return BASE.seal(
        {
            "schema": SHARD_SCHEMA,
            "shard_id": M2.SHARD_ID,
            "shard_sha256": M2.SHARD_SHA256,
            "case_ids_sha256": M2.SHARD_CASE_IDS_SHA256,
            "case_count": M2.SHARD_CASE_COUNT,
            "ordinal": 1,
            "start_offset": 64,
            "end_offset": 128,
            "historical_observation_case_ids": [],
            "case_refs": [
                {"id": case["id"], "registration_sha256": case["sha256"]}
                for case in contract["cases"]
            ],
            "parent_selection_id": M2.PARENT_SELECTION_ID,
            "parent_selection_sha256": M2.PARENT_SELECTION_SHA256,
            "parent_selected_count": M2.PARENT_SELECTED_COUNT,
            "parent_completed": False,
            "record_sha256": "",
        },
        SHARD_SCHEMA,
    )


def build_run_record(
    *,
    spec: dict[str, Any],
    source: dict[str, Any],
    toolchain: dict[str, Any],
    tools: dict[str, Any],
    platform: dict[str, Any],
    lane: dict[str, Any],
    shard: dict[str, Any],
    harness: dict[str, Any],
    discovery: dict[str, Any],
    storage: dict[str, Any],
) -> dict[str, Any]:
    return BASE.seal(
        {
            "schema": RUN_SCHEMA,
            "run_id": M2.RUN_ID,
            "attempt_id": M2.ATTEMPT_ID,
            "sequence": M2.SEQUENCE,
            "implementation_revision": spec["implementation_revision"],
            "spec_sha256": spec["record_sha256"],
            "source_sha256": source["record_sha256"],
            "toolchain_sha256": toolchain["record_sha256"],
            "tools_sha256": tools["record_sha256"],
            "platform_sha256": platform["record_sha256"],
            "lane_sha256": lane["record_sha256"],
            "shard_record_sha256": shard["record_sha256"],
            "harness_sha256": harness["record_sha256"],
            "discovery_sha256": discovery["record_sha256"],
            "command": spec["command"],
            "command_sha256": BASE.digest(spec["command"]),
            "working_directory": spec["working_directory"],
            "environment": spec["environment"],
            "environment_sha256": BASE.digest(spec["environment"]),
            "resource_envelope": spec["resource_envelope"],
            "resource_envelope_sha256": BASE.digest(spec["resource_envelope"]),
            "storage_class": storage,
            "storage_class_sha256": storage["identity_sha256"],
            "credit_class": "local-official-shard-outcomes-only",
            "record_sha256": "",
        },
        RUN_SCHEMA,
    )


def build_prelaunch_record(
    *, spec: dict[str, Any], run: dict[str, Any], shard: dict[str, Any]
) -> dict[str, Any]:
    return BASE.seal(
        {
            "schema": PRELAUNCH_SCHEMA,
            "run_id": M2.RUN_ID,
            "attempt_id": M2.ATTEMPT_ID,
            "sequence": M2.SEQUENCE,
            "spec_sha256": spec["record_sha256"],
            "run_sha256": run["record_sha256"],
            "shard_record_sha256": shard["record_sha256"],
            "recorded_before_launch": True,
            "terminal": None,
            "selection_case_ids": M2.selected_contract()["shard"]["case_ids"],
            "case_records": [],
            "record_sha256": "",
        },
        PRELAUNCH_SCHEMA,
    )


def validate_platform_record(record: Any) -> list[str]:
    if not BASE.valid_seal(record, PLATFORM_SCHEMA):
        return ["M2 platform record identity drift"]
    failures = []
    platform = record.get("platform", {})
    if (
        not isinstance(record.get("captured_utc"), str)
        or not record["captured_utc"].endswith("Z")
        or not isinstance(platform, dict)
        or platform.get("provider") != "local-process"
        or not isinstance(record.get("uname"), list)
        or len(record["uname"]) != 5
        or not isinstance(record.get("glibc"), str)
        or not record["glibc"]
        or (
            record.get("online_cpu_count") is not None
            and (
                not isinstance(record["online_cpu_count"], int)
                or record["online_cpu_count"] <= 0
            )
        )
        or record.get("official_provider_claimed") is not False
    ):
        failures.append("M2 platform field or provider drift")
    return failures


def validate_lane_record(record: Any) -> list[str]:
    return [] if record == build_lane_record() else ["M2 lane record drift"]


def validate_shard_record(record: Any) -> list[str]:
    return [] if record == build_shard_record() else ["M2 shard record drift"]


def validate_discovery_record(
    record: Any,
    *,
    spec: dict[str, Any],
    harness: dict[str, Any],
    raw: bytes,
) -> list[str]:
    if not BASE.valid_seal(record, DISCOVERY_SCHEMA):
        return ["M2 discovery record identity drift"]
    expected_command = [
        "/usr/bin/ctest",
        "--test-dir",
        spec["harness_build"],
        "--show-only=json-v1",
        "-E",
        "foreign",
    ]
    normalized = harness.get("discovery")
    if (
        record.get("command") != expected_command
        or record.get("raw") != _descriptor("raw/discovery.json", raw)
        or record.get("normalized") != normalized
        or record.get("normalized_sha256")
        != BASE.domain_digest(
            "axeyum-lean-u2-official-execution-m2-discovery-v1", normalized
        )
    ):
        return ["M2 discovery command, raw, or normalized projection drift"]
    return []


def validate_run_record(
    record: Any,
    *,
    spec: dict[str, Any],
    source: dict[str, Any],
    toolchain: dict[str, Any],
    tools: dict[str, Any],
    platform: dict[str, Any],
    lane: dict[str, Any],
    shard: dict[str, Any],
    harness: dict[str, Any],
    discovery: dict[str, Any],
) -> list[str]:
    if not isinstance(record, dict):
        return ["M2 run record is not an object"]
    storage = record.get("storage_class")
    storage_failures = BASE.STORE.validate_storage_descriptor(storage)
    if storage_failures:
        return ["M2 run storage drift: " + "; ".join(storage_failures)]
    expected = build_run_record(
        spec=spec,
        source=source,
        toolchain=toolchain,
        tools=tools,
        platform=platform,
        lane=lane,
        shard=shard,
        harness=harness,
        discovery=discovery,
        storage=storage,
    )
    return [] if record == expected else ["M2 run record linkage drift"]


def validate_prelaunch_record(
    record: Any,
    *,
    spec: dict[str, Any],
    run: dict[str, Any],
    shard: dict[str, Any],
) -> list[str]:
    expected = build_prelaunch_record(spec=spec, run=run, shard=shard)
    return [] if record == expected else ["M2 prelaunch record drift"]


def validate_terminal_record(
    record: Any,
    *,
    prelaunch: dict[str, Any],
    stdout: bytes,
    stderr: bytes,
    require_eligible: bool,
) -> list[str]:
    if not BASE.valid_seal(record, TERMINAL_SCHEMA):
        return ["M2 terminal record identity drift"]
    failures = []
    process = record.get("process", {})
    terminal_class = record.get("class")
    expected_raw = [
        _descriptor("raw/stderr.bin", stderr),
        _descriptor("raw/stdout.bin", stdout),
    ]
    wall = record.get("wall_time", {})
    cpu = record.get("cpu_time", {})
    peak = record.get("peak_rss", {})
    if (
        record.get("run_id") != M2.RUN_ID
        or record.get("attempt_id") != M2.ATTEMPT_ID
        or record.get("sequence") != M2.SEQUENCE
        or record.get("prelaunch_sha256") != prelaunch.get("record_sha256")
        or record.get("raw_outputs") != expected_raw
        or not isinstance(record.get("events"), list)
        or not isinstance(process, dict)
        or process.get("live_non_zombie_pids_after_cleanup") != []
        or wall.get("state") != "observed"
        or not isinstance(wall.get("value"), int)
        or wall["value"] < 1
        or wall.get("unit") != "milliseconds"
        or cpu != BASE.metric("not-observed", None, "milliseconds")
        or peak.get("unit") != "bytes"
        or peak.get("state") not in {"observed", "not-observed"}
        or (
            peak.get("state") == "observed"
            and (not isinstance(peak.get("value"), int) or peak["value"] < 0)
        )
        or (peak.get("state") == "not-observed" and peak.get("value") is not None)
    ):
        failures.append("M2 terminal attribution, raw output, or cleanup drift")
    if terminal_class == "exited":
        if (
            not isinstance(record.get("exit_code"), int)
            or record["exit_code"] < 0
            or record.get("signal") is not None
            or process.get("rlimit_as_bytes") != M2.MEMORY_LIMIT_BYTES
            or process.get("watchdog_fired") is not False
            or process.get("direct_child_reaped") is not True
            or record.get("launch_diagnostic") is not None
        ):
            failures.append("M2 exited terminal field drift")
    elif terminal_class == "launch-failed":
        if (
            record.get("exit_code") is not None
            or record.get("signal") is not None
            or process.get("pid") is not None
            or process.get("rlimit_as_bytes") is not None
            or process.get("direct_child_reaped") is not False
            or not isinstance(record.get("launch_diagnostic"), str)
        ):
            failures.append("M2 launch-failed terminal field drift")
    elif terminal_class == "wall-timeout":
        if process.get("watchdog_fired") is not True or process.get(
            "direct_child_reaped"
        ) is not True:
            failures.append("M2 wall-timeout terminal field drift")
    elif terminal_class == "signaled":
        if (
            not isinstance(record.get("signal"), int)
            or record["signal"] <= 0
            or record.get("exit_code") is not None
            or process.get("direct_child_reaped") is not True
        ):
            failures.append("M2 signaled terminal field drift")
    else:
        failures.append("M2 terminal class drift")
    if require_eligible and (
        terminal_class != "exited"
        or record.get("exit_code") not in {0, 8}
        or process.get("watchdog_fired") is not False
        or process.get("direct_child_reaped") is not True
        or not isinstance(process.get("pid"), int)
        or process.get("pid") <= 0
        or process.get("process_group_id") != process.get("pid")
        or process.get("sigterm_sent") is not False
        or process.get("sigkill_sent") is not False
        or record.get("events")
        != [
            "prelaunch-record-installed",
            "rlimit-as-installed",
            "direct-child-reaped",
            "process-group-no-live-members-observed",
        ]
    ):
        failures.append("M2 terminal is not eligible for case outcomes")
    return failures


def execute_process(
    spec: dict[str, Any],
    private_root: Path,
    prelaunch_sha256: str,
    *,
    popen_factory: Callable[..., subprocess.Popen[bytes]] = subprocess.Popen,
    live_members: Callable[[int], list[int]] = BASE.PROCESS._live_process_group_members,
    sample_rss: Callable[[int], int | None] = BASE.PROCESS._sample_peak_rss,
) -> tuple[dict[str, Any], bytes, bytes]:
    failures = M2.validate_spec(spec)
    if failures:
        raise M2RunError("; ".join(failures))
    private = private_root.resolve()
    if private.exists() or private.is_symlink():
        raise M2RunError("M2 private attempt directory must be new")
    private.mkdir(parents=True, mode=0o700)
    stdout_path = private / "stdout.bin"
    stderr_path = private / "stderr.bin"
    process: subprocess.Popen[bytes] | None = None
    peak_rss: int | None = None
    events = ["prelaunch-record-installed"]
    watchdog = False
    sigterm_sent = False
    sigkill_sent = False
    direct_child_reaped = False
    live: list[int] = []
    launch_diagnostic: str | None = None
    start_ns = time.monotonic_ns()
    with stdout_path.open("xb", buffering=0) as stdout_handle, stderr_path.open(
        "xb", buffering=0
    ) as stderr_handle:
        try:
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
                preexec_fn=BASE.PROCESS._limit_hook(M2.MEMORY_LIMIT_BYTES),
            )
        except (OSError, subprocess.SubprocessError) as error:
            launch_diagnostic = f"{type(error).__name__}-errno-{getattr(error, 'errno', None)}"
            events.append("launch-error-observed")
        if process is not None:
            pid = process.pid
            pgid = process.pid
            events.append("rlimit-as-installed")
            deadline_ns = start_ns + M2.WALL_TIMEOUT_MS * 1_000_000
            while process.poll() is None and time.monotonic_ns() < deadline_ns:
                sampled = sample_rss(pid)
                if sampled is not None:
                    peak_rss = max(peak_rss or 0, sampled)
                time.sleep(0.01)
            if process.poll() is None:
                watchdog = True
                events.append("wall-timeout-observed")
                try:
                    os.killpg(pgid, signal.SIGTERM)
                    sigterm_sent = True
                    events.append("process-group-sigterm-sent")
                except ProcessLookupError:
                    pass
                grace = time.monotonic_ns() + M2.TERMINATE_GRACE_MS * 1_000_000
                while time.monotonic_ns() < grace and live_members(pgid):
                    time.sleep(0.01)
                if live_members(pgid):
                    try:
                        os.killpg(pgid, signal.SIGKILL)
                        sigkill_sent = True
                        events.append("process-group-sigkill-sent")
                    except ProcessLookupError:
                        pass
            try:
                process.wait(timeout=3)
                direct_child_reaped = True
                events.append("direct-child-reaped")
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(pgid, signal.SIGKILL)
                    sigkill_sent = True
                except ProcessLookupError:
                    pass
                process.wait(timeout=3)
                direct_child_reaped = True
                events.append("direct-child-reaped")
            live = live_members(pgid)
            cleanup_deadline = time.monotonic_ns() + 1_000_000_000
            while live and time.monotonic_ns() < cleanup_deadline:
                time.sleep(0.01)
                live = live_members(pgid)
            if not live:
                events.append("process-group-no-live-members-observed")
        stdout_handle.flush()
        stderr_handle.flush()
        os.fsync(stdout_handle.fileno())
        os.fsync(stderr_handle.fileno())
    stdout = stdout_path.read_bytes()
    stderr = stderr_path.read_bytes()
    elapsed_ms = max(1, (time.monotonic_ns() - start_ns) // 1_000_000)
    return_code = process.returncode if process is not None else None
    terminal_class = (
        "launch-failed"
        if process is None
        else "wall-timeout"
        if watchdog
        else "signaled"
        if return_code is not None and return_code < 0
        else "exited"
    )
    terminal = BASE.seal(
        {
            "schema": TERMINAL_SCHEMA,
            "run_id": M2.RUN_ID,
            "attempt_id": M2.ATTEMPT_ID,
            "sequence": M2.SEQUENCE,
            "prelaunch_sha256": prelaunch_sha256,
            "class": terminal_class,
            "exit_code": return_code if return_code is not None and return_code >= 0 else None,
            "signal": -return_code if return_code is not None and return_code < 0 else None,
            "events": events,
            "wall_time": BASE.metric("observed", elapsed_ms, "milliseconds"),
            "cpu_time": BASE.metric("not-observed", None, "milliseconds"),
            "peak_rss": (
                BASE.metric("observed", peak_rss, "bytes")
                if peak_rss is not None
                else BASE.metric("not-observed", None, "bytes")
            ),
            "process": {
                "pid": process.pid if process is not None else None,
                "process_group_id": process.pid if process is not None else None,
                "rlimit_as_bytes": (
                    M2.MEMORY_LIMIT_BYTES if process is not None else None
                ),
                "watchdog_fired": watchdog,
                "sigterm_sent": sigterm_sent,
                "sigkill_sent": sigkill_sent,
                "direct_child_reaped": direct_child_reaped,
                "live_non_zombie_pids_after_cleanup": live,
            },
            "launch_diagnostic": launch_diagnostic,
            "raw_outputs": [
                _descriptor("raw/stderr.bin", stderr),
                _descriptor("raw/stdout.bin", stdout),
            ],
            "record_sha256": "",
        },
        TERMINAL_SCHEMA,
    )
    return terminal, stdout, stderr


def capture_post(
    *,
    source_root: Path,
    source: dict[str, Any],
    wrapper: bytes,
    junit: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, bytes]]:
    before = {row["path"]: row for row in source["files"]}
    after_rows = BASE.manifest_tree(source_root)
    after = {row["path"]: row for row in after_rows}
    changed = [path for path, row in before.items() if after.get(path) != row]
    if changed:
        raise M2RunError("official source or sidecar mutated: " + ", ".join(changed[:5]))
    new_paths = sorted(set(after) - set(before))
    generated = [after[path] for path in new_paths]
    try:
        post = M2.build_post_record(
            original_files=source["files"], generated_files=generated, junit=junit
        )
    except M2.M2ContractError as error:
        raise M2RunError(str(error)) from error
    payloads = {path: (source_root / path).read_bytes() for path in new_paths}
    if payloads.get("tests/with_stage1_test_env.sh") != wrapper:
        raise M2RunError("M2 generated environment wrapper mutated")
    return post, payloads


def _install_prelaunch(
    evidence_root: Path,
    *,
    records: dict[str, dict[str, Any]],
    wrapper: bytes,
    ctest: bytes,
    raw_discovery: bytes,
) -> None:
    evidence_root.mkdir(parents=True, mode=0o755)
    for relative in (
        "source.json",
        "toolchain.json",
        "tools.json",
        "platform.json",
        "lane.json",
        "run.json",
        "shard.json",
        "harness.json",
        "discovery.json",
        "spec.json",
        "prelaunch.json",
    ):
        BASE.install_json(evidence_root, relative, records[relative])
    BASE.install_bytes(
        evidence_root, "artifacts/with_stage1_test_env.sh", wrapper
    )
    BASE.install_bytes(evidence_root, "artifacts/CTestTestfile.cmake", ctest)
    BASE.install_bytes(evidence_root, "raw/discovery.json", raw_discovery)
    BASE.validate_live_readonly_tree(evidence_root)


def validate_complete_evidence(root: Path) -> dict[str, Any]:
    completion = M2_STORE.validate_complete_store(root)
    source = BASE.load_canonical(root / "source.json")
    toolchain = BASE.load_canonical(root / "toolchain.json")
    tools = BASE.load_canonical(root / "tools.json")
    platform = BASE.load_canonical(root / "platform.json")
    lane = BASE.load_canonical(root / "lane.json")
    run = BASE.load_canonical(root / "run.json")
    shard = BASE.load_canonical(root / "shard.json")
    harness = BASE.load_canonical(root / "harness.json")
    discovery = BASE.load_canonical(root / "discovery.json")
    spec = BASE.load_canonical(root / "spec.json")
    prelaunch = BASE.load_canonical(root / "prelaunch.json")
    terminal = BASE.load_canonical(root / "terminal.json")
    raw_discovery = (root / "raw/discovery.json").read_bytes()
    stdout = (root / "raw/stdout.bin").read_bytes()
    stderr = (root / "raw/stderr.bin").read_bytes()
    failures = [
        *validate_selected_source(source),
        *R2.validate_toolchain_record(toolchain),
        *BASE.validate_local_tools(tools),
        *validate_platform_record(platform),
        *validate_lane_record(lane),
        *validate_shard_record(shard),
        *validate_discovery_record(
            discovery,
            spec=spec,
            harness=harness,
            raw=raw_discovery,
        ),
        *validate_run_record(
            run,
            spec=spec,
            source=source,
            toolchain=toolchain,
            tools=tools,
            platform=platform,
            lane=lane,
            shard=shard,
            harness=harness,
            discovery=discovery,
        ),
        *validate_prelaunch_record(
            prelaunch,
            spec=spec,
            run=run,
            shard=shard,
        ),
        *validate_terminal_record(
            terminal,
            prelaunch=prelaunch,
            stdout=stdout,
            stderr=stderr,
            require_eligible=True,
        ),
    ]
    try:
        discovery_payload = json.loads(raw_discovery)
        expected_harness = M2.build_harness_record(
            source_root=Path(spec["source_root"]),
            toolchain_root=Path(spec["toolchain_root"]),
            harness_root=Path(spec["harness_build"]),
            discovery_payload=discovery_payload,
        )
        expected_wrapper = M2.render_environment_wrapper(
            Path(spec["source_root"]), Path(spec["toolchain_root"])
        )
        expected_ctest = M2.render_ctest_file(
            source_root=Path(spec["source_root"]),
            toolchain_root=Path(spec["toolchain_root"]),
            harness_root=Path(spec["harness_build"]),
        )
    except (KeyError, TypeError, json.JSONDecodeError, M2.M2ContractError) as error:
        failures.append(f"M2 retained harness cannot be reconstructed: {error}")
    else:
        if harness != expected_harness:
            failures.append("M2 retained harness semantic drift")
        if (root / "artifacts/with_stage1_test_env.sh").read_bytes() != expected_wrapper:
            failures.append("M2 retained wrapper semantic drift")
        if (root / "artifacts/CTestTestfile.cmake").read_bytes() != expected_ctest:
            failures.append("M2 retained CTest file semantic drift")
    if failures:
        raise M2RunError("; ".join(failures))
    return completion


def run_m2(args: argparse.Namespace) -> None:
    M2.validate_offline_contract()
    M2_STORE.validate_offline_contract()
    validate_revision_preflight(args.implementation_revision)
    if args.work_root.exists() or args.work_root.is_symlink():
        raise M2RunError("M2 private work root must be new")
    if args.evidence_root.exists() or args.evidence_root.is_symlink():
        raise M2RunError("M2 evidence root must be new")
    args.work_root.mkdir(parents=True, mode=0o700)
    source_root = args.work_root / "source"
    harness_root = args.work_root / "harness"
    private_root = args.work_root / "attempt"
    junit_path = private_root / "test-results.xml"

    source = capture_source(args.source_repo, source_root)
    toolchain = capture_toolchain(args.toolchain_root, args.work_root)
    tools = BASE.capture_local_tools()
    tool_failures = BASE.validate_local_tools(tools)
    if tool_failures:
        raise M2RunError("; ".join(tool_failures))
    harness, discovery, wrapper, ctest, raw_discovery = prepare_harness(
        source_root=source_root,
        toolchain_root=args.toolchain_root,
        harness_root=harness_root,
    )
    spec = M2.build_spec(
        implementation_revision=args.implementation_revision,
        source_root=source_root,
        toolchain_root=args.toolchain_root,
        harness_build=harness_root,
        junit_path=junit_path,
    )
    spec_failures = M2.validate_spec(spec)
    if spec_failures:
        raise M2RunError("; ".join(spec_failures))
    platform = build_platform_record(source_root)
    lane = build_lane_record()
    shard = build_shard_record()
    storage = BASE.STORE.capture_storage_class(BASE.STORE.STORAGE_CLASS_IDS[0], ROOT)
    BASE.STORE.preflight_storage_class(storage)
    run = build_run_record(
        spec=spec,
        source=source,
        toolchain=toolchain,
        tools=tools,
        platform=platform,
        lane=lane,
        shard=shard,
        harness=harness,
        discovery=discovery,
        storage=storage,
    )
    prelaunch = build_prelaunch_record(spec=spec, run=run, shard=shard)
    records = {
        "source.json": source,
        "toolchain.json": toolchain,
        "tools.json": tools,
        "platform.json": platform,
        "lane.json": lane,
        "run.json": run,
        "shard.json": shard,
        "harness.json": harness,
        "discovery.json": discovery,
        "spec.json": spec,
        "prelaunch.json": prelaunch,
    }
    _install_prelaunch(
        args.evidence_root,
        records=records,
        wrapper=wrapper,
        ctest=ctest,
        raw_discovery=raw_discovery,
    )

    terminal, stdout, stderr = execute_process(
        spec, private_root, prelaunch["record_sha256"]
    )
    BASE.install_bytes(args.evidence_root, "raw/stdout.bin", stdout)
    BASE.install_bytes(args.evidence_root, "raw/stderr.bin", stderr)
    BASE.install_json(args.evidence_root, "terminal.json", terminal)
    BASE.validate_live_readonly_tree(args.evidence_root)
    process = terminal["process"]
    if (
        terminal["class"] != "exited"
        or terminal["exit_code"] not in {0, 8}
        or terminal["signal"] is not None
        or process["watchdog_fired"]
        or not process["direct_child_reaped"]
        or process["live_non_zombie_pids_after_cleanup"] != []
    ):
        raise M2RunError("M2 CTest process did not close as an eligible exited group")
    if not junit_path.is_file() or junit_path.is_symlink():
        raise M2RunError("M2 CTest process produced no regular JUnit file")
    raw_junit = junit_path.read_bytes()
    BASE.install_bytes(args.evidence_root, "raw/junit.xml", raw_junit)
    try:
        junit = M2.parse_junit(raw_junit, terminal)
    except M2.M2ContractError as error:
        raise M2RunError(str(error)) from error
    BASE.install_json(args.evidence_root, "junit.json", junit)

    cases = M2.build_case_records(spec=spec, terminal=terminal, junit=junit)
    for ordinal, case in enumerate(cases):
        BASE.install_json(args.evidence_root, M2_STORE.case_path(ordinal), case)

    post, generated = capture_post(
        source_root=source_root, source=source, wrapper=wrapper, junit=junit
    )
    for source_path, payload in generated.items():
        BASE.install_bytes(
            args.evidence_root, M2_STORE.generated_path(source_path), payload
        )
    BASE.install_json(args.evidence_root, "post.json", post)
    projection = M2.result_projection(junit, post)
    BASE.install_json(args.evidence_root, "projection.json", projection)
    completion = M2_STORE.install_completion(args.evidence_root)
    validate_complete_evidence(args.evidence_root)
    BASE.validate_live_readonly_tree(args.evidence_root)
    print(
        "LEAN_U2_M2_RUN|"
        f"cases={projection['credits']['official_cases']}|"
        f"passes={projection['credits']['official_passes']}|"
        f"failures={projection['credits']['official_failures']}|"
        f"completion={completion['record_sha256']}|"
        "parent_complete=false|provider=false|axeyum=0|pairs=0|parity=0"
    )


def validate_offline_runner() -> dict[str, Any]:
    if (
        not M2.HEX40.fullmatch(R1_PREREGISTRATION_COMMIT)
        or not R1_PLAN.is_file()
        or BASE.sha256_file(R1_PLAN) != R1_PLAN_SHA256
    ):
        raise M2RunError("M2 R1 symlink-preflight plan drift")
    contract = M2.validate_offline_contract()
    store = M2_STORE.validate_offline_contract()
    lane = build_lane_record()
    shard = build_shard_record()
    if lane["resource_envelope"] != M2.resource_envelope():
        raise M2RunError("M2 runner lane drift")
    if len(shard["case_refs"]) != M2.SHARD_CASE_COUNT:
        raise M2RunError("M2 runner shard drift")
    return {
        "cases": contract["case_count"],
        "store_cases": store["case_records"],
        "lane": lane["lane_id"],
        "r1_preregistration_commit": R1_PREREGISTRATION_COMMIT,
        "r1_plan_sha256": R1_PLAN_SHA256,
        "run_command_exposed": True,
        "live_execution_observed": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command_name", required=True)
    commands.add_parser("offline-check")
    run = commands.add_parser("run-m2")
    run.add_argument("--implementation-revision", required=True)
    run.add_argument("--source-repo", type=Path, required=True)
    run.add_argument("--toolchain-root", type=Path, required=True)
    run.add_argument("--work-root", type=Path, required=True)
    run.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    validate = commands.add_parser("validate")
    validate.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    args = parser.parse_args()
    try:
        if args.command_name == "offline-check":
            summary = validate_offline_runner()
            print(
                "LEAN_U2_M2_RUNNER|"
                f"cases={summary['cases']}|store_cases={summary['store_cases']}|"
                f"lane={summary['lane']}|run_command=true|"
                "live_execution_observed=false|outcomes=0|parity=0"
            )
        elif args.command_name == "run-m2":
            run_m2(args)
        elif args.command_name == "validate":
            completion = validate_complete_evidence(args.evidence_root)
            print(
                "LEAN_U2_M2_EVIDENCE_VALID|"
                f"completion={completion['record_sha256']}|"
                "cases=64|parent_complete=false|parity=0"
            )
        else:  # pragma: no cover
            raise AssertionError(args.command_name)
    except (
        BASE.U2ExecutionError,
        BASE.STORE.CheckpointConflict,
        BASE.STORE.StoreEvidenceError,
        M2.M2ContractError,
        M2_STORE.M2StoreError,
        M2RunError,
    ) as error:
        print(f"LEAN_U2_M2_RUN_ERROR|{error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
