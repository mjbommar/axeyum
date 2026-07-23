#!/usr/bin/env python3
"""Run and validate the source-first M2 R4 attempt-003 contract.

Offline validation never starts Lean or constructs the selected CTest harness.
``run-r4`` is the only selected-execution surface; it runs both harmless
released-Lean controls before constructing the harness.
"""

from __future__ import annotations

import argparse
import json
import os
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
from scripts import lean_u2_official_execution_m2_run as OLD_RUN  # noqa: E402
from scripts import lean_u2_official_execution_m2_store as OLD_STORE  # noqa: E402


PLAN = ROOT / (
    "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r4-"
    "attempt-003-plan-2026-07-23.md"
)
PREREGISTRATION_COMMIT = "42b3e6b2ca7327763f3fd57fef70d0421f8950dc"
PLAN_SHA256 = "b38566390250d98d3e4c1667c6a3a4215ac5ac962cdc96686b0c7fc6a2307d1e"
R3_AUTHORITY = ROOT / (
    "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r3-"
    "attempt-002-result-v1.json"
)
R3_AUTHORITY_FILE_SHA256 = (
    "13ac5126e964aa997504dc3e8da06524849fbe91015cfff53e8ed026c4f8eae2"
)
R3_AUTHORITY_RECORD = (
    "e972d2ec0d69f1d38f9d0844295585b03d9b80433bf56c23b7b8392ca0af1dbc"
)
R3_TERMINAL_RECORD = (
    "c228a80ef0dec5204a2cd1d9478faef8273f778bf36c12c6d2fbd31262b7c6f6"
)

RUN_ID = "tl0.6.3-m2-release-linux-shard-0001-v3"
ATTEMPT_ID = "attempt-003"
SEQUENCE = 3
LANE_ID = "official-ctest-local-16g-lean-j1-stack512m-shard64-v3"
MEMORY_LIMIT_BYTES = 17_179_869_184
STACK_SIZE_KB = R3.STACK_SIZE_KB
STACK_SIZE_BYTES = R3.STACK_SIZE_BYTES
STACK_ENV = R3.STACK_ENV

DEFAULT_SOURCE_REPO = R3.DEFAULT_SOURCE_REPO
DEFAULT_TOOLCHAIN_ROOT = R3.DEFAULT_TOOLCHAIN_ROOT
DEFAULT_EVIDENCE_ROOT = ROOT / (
    "docs/plan/evidence/"
    "lean-u2-official-execution-tl0.6.3-m2-shard-0001-r4-attempt-003"
)
WORK_ROOT_PREFIX = "/home/mjbommar/.cache/axeyum-tl063-m2-r4-"

COMPLETION_SCHEMA = "axeyum-lean-u2-official-execution-m2-r4-completion-v1"
RECORD_SET_DOMAIN = "axeyum-lean-u2-official-execution-m2-r4-record-set-v1"
FULL_DOMAIN = "axeyum-lean-u2-official-execution-m2-r4-generated-files-v1"
RETAINED_DOMAIN = "axeyum-lean-u2-official-execution-m2-r4-retained-files-v1"
METADATA_DOMAIN = "axeyum-lean-u2-official-execution-m2-r4-metadata-files-v1"
ALLOWED_DOMAIN = "axeyum-lean-u2-official-execution-m2-r4-allowed-paths-v1"

FANOUT_SCHEMA = "axeyum-lean-u2-official-execution-m2-r4-fanout-control-v1"
FANOUT_SUCCESS = b"R4_FANOUT_OK|tasks=9|sum=36\n"
FANOUT_SOURCE = '''def main : IO Unit := do
  let tasks <- (List.range 9).mapM fun i => IO.asTask (prio := .dedicated) (pure i)
  let values <- tasks.mapM fun task => do IO.ofExcept (← IO.wait task)
  IO.println s!"R4_FANOUT_OK|tasks={values.length}|sum={values.foldl (fun a b => a + b) 0}"
'''.encode("utf-8")

_R3_BUILD_SPEC = R3.build_spec
_R3_RENDER_WRAPPER = R3.render_environment_wrapper
_R3_BUILD_HARNESS = R3.build_harness_record
_R3_BUILD_POST = R3.build_post_record
_R3_RESULT_PROJECTION = R3.result_projection


class R4Error(ValueError):
    """The R4 preregistration, execution, or evidence closure drifted."""


def validate_history() -> dict[str, Any]:
    R3.validate_history()
    incomplete = R3.validate_incomplete_evidence(R3.DEFAULT_EVIDENCE_ROOT)
    if (
        not M2.HEX40.fullmatch(PREREGISTRATION_COMMIT)
        or not PLAN.is_file()
        or BASE.sha256_file(PLAN) != PLAN_SHA256
        or not R3_AUTHORITY.is_file()
        or BASE.sha256_file(R3_AUTHORITY) != R3_AUTHORITY_FILE_SHA256
    ):
        raise R4Error("R4 preregistration or R3 authority identity drift")
    authority = BASE.load_json(R3_AUTHORITY)
    credits = authority.get("credits", {}) if isinstance(authority, dict) else {}
    if (
        not isinstance(authority, dict)
        or not BASE.valid_seal(authority, authority.get("schema", ""))
        or authority.get("record_sha256") != R3_AUTHORITY_RECORD
        or authority.get("status") != "invalid-wall-timeout"
        or authority.get("terminal", {}).get("record_sha256") != R3_TERMINAL_RECORD
        or authority.get("retained_evidence", {}).get("files") != 17
        or authority.get("retained_evidence", {}).get("bytes") != 4_908_035
        or any(value != 0 for value in credits.values())
        or incomplete["official_outcomes"] != 0
    ):
        raise R4Error("R3 immutable result authority drift")
    return {"authority": authority, "incomplete": incomplete}


def resource_envelope() -> dict[str, Any]:
    envelope = dict(R3.ORIG_RESOURCE_ENVELOPE())
    envelope.update(
        {
            "lane_id": LANE_ID,
            "memory_limit": BASE.metric("observed", MEMORY_LIMIT_BYTES, "bytes"),
            "task_stack_limit": BASE.metric(
                "requested", STACK_SIZE_BYTES, "bytes"
            ),
            "task_stack_policy": "universal-LEAN_STACK_SIZE_KB-environment",
            "task_stack_enforcement": STACK_ENV,
        }
    )
    return envelope


def build_spec(
    *,
    implementation_revision: str,
    source_root: Path,
    toolchain_root: Path,
    harness_build: Path,
    junit_path: Path,
) -> dict[str, Any]:
    spec = _R3_BUILD_SPEC(
        implementation_revision=implementation_revision,
        source_root=source_root,
        toolchain_root=toolchain_root,
        harness_build=harness_build,
        junit_path=junit_path,
    )
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
            "r3_authority_file_sha256": R3_AUTHORITY_FILE_SHA256,
            "r3_authority_record_sha256": R3_AUTHORITY_RECORD,
            "r3_terminal_record_sha256": R3_TERMINAL_RECORD,
        }
    )
    spec["record_sha256"] = ""
    return BASE.seal(spec, M2.SPEC_SCHEMA)


def validate_spec(spec: Any) -> list[str]:
    if not isinstance(spec, dict) or not BASE.valid_seal(spec, M2.SPEC_SCHEMA):
        return ["R4 spec identity drift"]
    try:
        expected = build_spec(
            implementation_revision=spec["implementation_revision"],
            source_root=Path(spec["source_root"]),
            toolchain_root=Path(spec["toolchain_root"]),
            harness_build=Path(spec["harness_build"]),
            junit_path=Path(spec["junit_path"]),
        )
    except (KeyError, TypeError, R3.R3Error, R4Error) as error:
        return [f"R4 spec cannot be reconstructed: {error}"]
    return [] if spec == expected else ["R4 spec field or linkage drift"]


def render_environment_wrapper(source_root: Path, toolchain_root: Path) -> bytes:
    return _R3_RENDER_WRAPPER(source_root, toolchain_root)


def build_harness_record(**kwargs: Any) -> dict[str, Any]:
    return _R3_BUILD_HARNESS(**kwargs)


def build_post_record(**kwargs: Any) -> dict[str, Any]:
    return _R3_BUILD_POST(**kwargs)


def result_projection(junit: dict[str, Any], post: dict[str, Any]) -> dict[str, Any]:
    return _R3_RESULT_PROJECTION(junit, post)


@contextmanager
def r4_bindings() -> Iterator[None]:
    m2_bindings = {
        "RUN_ID": RUN_ID,
        "ATTEMPT_ID": ATTEMPT_ID,
        "SEQUENCE": SEQUENCE,
        "LANE_ID": LANE_ID,
        "MEMORY_LIMIT_BYTES": MEMORY_LIMIT_BYTES,
        "resource_envelope": resource_envelope,
        "build_spec": build_spec,
        "validate_spec": validate_spec,
        "render_environment_wrapper": render_environment_wrapper,
        "build_harness_record": build_harness_record,
        "case_generated_paths": R3.case_generated_paths,
        "declared_generated_paths": R3.declared_generated_paths,
        "build_post_record": build_post_record,
        "result_projection": result_projection,
    }
    r3_bindings = {
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
        "render_environment_wrapper": render_environment_wrapper,
        "build_harness_record": build_harness_record,
        "build_post_record": build_post_record,
        "result_projection": result_projection,
    }
    previous_m2 = {name: getattr(M2, name) for name in m2_bindings}
    previous_r3 = {name: getattr(R3, name) for name in r3_bindings}
    try:
        for name, value in m2_bindings.items():
            setattr(M2, name, value)
        for name, value in r3_bindings.items():
            setattr(R3, name, value)
        yield
    finally:
        for name, value in previous_r3.items():
            setattr(R3, name, value)
        for name, value in previous_m2.items():
            setattr(M2, name, value)


def probe_stack_environment(
    toolchain_root: Path,
    *,
    run_command: Callable[..., subprocess.CompletedProcess[bytes]] = subprocess.run,
) -> dict[str, Any]:
    return R3.probe_stack_environment(toolchain_root, run_command=run_command)


def probe_fanout(
    toolchain_root: Path,
    *,
    popen_factory: Callable[..., subprocess.Popen[bytes]] = subprocess.Popen,
    live_members: Callable[[int], list[int]] = BASE.PROCESS._live_process_group_members,
    sample_rss: Callable[[int], int | None] = BASE.PROCESS._sample_peak_rss,
) -> dict[str, Any]:
    toolchain = toolchain_root.resolve()
    lean = toolchain / "bin/lean"
    if not lean.is_file() or lean.is_symlink():
        raise R4Error("R4 fanout control lacks regular released Lean")
    environment = {
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        STACK_ENV: str(STACK_SIZE_KB),
        "PATH": f"{toolchain / 'bin'}:/usr/bin:/bin",
        "TZ": "UTC",
    }
    stdout = b""
    stderr = b""
    peak_rss: int | None = None
    live: list[int] = []
    start_ns = time.monotonic_ns()
    with tempfile.TemporaryDirectory(prefix="axeyum-m2-r4-fanout-probe-") as temporary:
        root = Path(temporary)
        source = root / "probe.lean"
        source.write_bytes(FANOUT_SOURCE)
        stdout_path = root / "stdout.bin"
        stderr_path = root / "stderr.bin"
        command = [str(lean), "--run", str(source)]
        with stdout_path.open("xb", buffering=0) as stdout_handle, stderr_path.open(
            "xb", buffering=0
        ) as stderr_handle:
            process = popen_factory(
                command,
                cwd=root,
                env=environment,
                stdin=subprocess.DEVNULL,
                stdout=stdout_handle,
                stderr=stderr_handle,
                shell=False,
                close_fds=True,
                start_new_session=True,
                preexec_fn=BASE.PROCESS._limit_hook(MEMORY_LIMIT_BYTES),
            )
            sampled = sample_rss(process.pid)
            if sampled is not None:
                peak_rss = sampled
            deadline = time.monotonic_ns() + 120_000_000_000
            while process.poll() is None and time.monotonic_ns() < deadline:
                sampled = sample_rss(process.pid)
                if sampled is not None:
                    peak_rss = max(peak_rss or 0, sampled)
                time.sleep(0.01)
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait(timeout=3)
            live = live_members(process.pid)
            if live:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                live = live_members(process.pid)
        stdout = stdout_path.read_bytes()
        stderr = stderr_path.read_bytes()
    elapsed_ms = max(1, (time.monotonic_ns() - start_ns) // 1_000_000)
    if process.returncode != 0 or stdout != FANOUT_SUCCESS or stderr or live:
        raise R4Error("R4 released-Lean fanout control failed or leaked a process")
    return BASE.seal(
        {
            "schema": FANOUT_SCHEMA,
            "selected_case": False,
            "assigned_case_ids": [],
            "source": {
                "bytes": len(FANOUT_SOURCE),
                "sha256": BASE.sha256_bytes(FANOUT_SOURCE),
            },
            "command": [str(lean), "--run", "<temporary>/probe.lean"],
            "environment": environment,
            "memory_limit": BASE.metric("observed", MEMORY_LIMIT_BYTES, "bytes"),
            "terminal": {
                "class": "exited",
                "exit_code": process.returncode,
                "signal": None,
                "wall_time": BASE.metric("observed", elapsed_ms, "milliseconds"),
                "peak_direct_rss": (
                    BASE.metric("observed", peak_rss, "bytes")
                    if peak_rss is not None
                    else BASE.metric("not-observed", None, "bytes")
                ),
                "stdout_sha256": BASE.sha256_bytes(stdout),
                "stderr_sha256": BASE.sha256_bytes(stderr),
            },
            "cleanup": {
                "direct_child_reaped": True,
                "live_non_zombie_pids_after_cleanup": live,
            },
            "success_line": FANOUT_SUCCESS.decode().rstrip("\n"),
            "credits": dict(M2.ZERO_TERMINAL_CREDITS),
            "record_sha256": "",
        },
        FANOUT_SCHEMA,
    )


def validate_revision_preflight(implementation_revision: str) -> None:
    OLD_RUN.validate_revision_preflight(implementation_revision)
    branch = OLD_RUN._git(ROOT, "branch", "--show-current")
    remote = OLD_RUN._git(ROOT, "ls-remote", "--heads", "origin", branch)
    fields = remote.split()
    if len(fields) != 2 or fields[0] != implementation_revision:
        raise R4Error("R4 implementation revision is not remote-equal")


def validate_live_paths(args: argparse.Namespace) -> None:
    expected_work = Path(WORK_ROOT_PREFIX + args.implementation_revision[:8])
    if args.work_root.resolve() != expected_work:
        raise R4Error("R4 work root is not the frozen revision-named path")
    if args.evidence_root.resolve() != DEFAULT_EVIDENCE_ROOT.resolve():
        raise R4Error("R4 evidence root substitution")
    if args.source_repo.resolve() != DEFAULT_SOURCE_REPO.resolve():
        raise R4Error("R4 source repository substitution")
    if args.toolchain_root.resolve() != DEFAULT_TOOLCHAIN_ROOT.resolve():
        raise R4Error("R4 released toolchain substitution")


def validate_complete_evidence(root: Path) -> dict[str, Any]:
    validate_history()
    with r4_bindings():
        return R3.validate_complete_evidence(root)


def validate_incomplete_evidence(root: Path) -> dict[str, Any]:
    """Validate a retained R4 wall timeout before any JUnit or case credit."""
    validate_history()
    with r4_bindings():
        result = R3.validate_incomplete_evidence(root)
    result["manifest_sha256"] = BASE.domain_digest(
        "axeyum-lean-u2-official-execution-m2-r4-incomplete-evidence-v1",
        R3.R2_DIAGNOSTIC.portable_manifest(root),
    )
    return result


def run_r4(args: argparse.Namespace) -> None:
    validate_offline_contract()
    validate_revision_preflight(args.implementation_revision)
    validate_live_paths(args)
    if args.work_root.exists() or args.work_root.is_symlink():
        raise R4Error("R4 private work root must be new")
    if args.evidence_root.exists() or args.evidence_root.is_symlink():
        raise R4Error("R4 evidence root must be new")
    probe_stack_environment(args.toolchain_root)
    control = probe_fanout(args.toolchain_root)
    if control["record_sha256"] != args.fanout_record_sha256:
        raise R4Error("R4 fanout control was not explicitly pre-observed")
    args.work_root.mkdir(parents=True, mode=0o700)
    source_root = args.work_root / "source"
    harness_root = args.work_root / "harness"
    private_root = args.work_root / "attempt"
    junit_path = private_root / "test-results.xml"
    with r4_bindings():
        source = OLD_RUN.capture_source(args.source_repo, source_root)
        toolchain = OLD_RUN.capture_toolchain(args.toolchain_root, args.work_root)
        tools = BASE.capture_local_tools()
        if failures := BASE.validate_local_tools(tools):
            raise R4Error("; ".join(failures))
        harness, discovery, wrapper, ctest, raw_discovery = OLD_RUN.prepare_harness(
            source_root=source_root,
            toolchain_root=args.toolchain_root,
            harness_root=harness_root,
        )
        spec = build_spec(
            implementation_revision=args.implementation_revision,
            source_root=source_root,
            toolchain_root=args.toolchain_root,
            harness_build=harness_root,
            junit_path=junit_path,
        )
        platform = OLD_RUN.build_platform_record(source_root)
        lane = OLD_RUN.build_lane_record()
        shard = OLD_RUN.build_shard_record()
        storage = BASE.STORE.capture_storage_class(BASE.STORE.STORAGE_CLASS_IDS[0], ROOT)
        BASE.STORE.preflight_storage_class(storage)
        run = OLD_RUN.build_run_record(
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
        prelaunch = OLD_RUN.build_prelaunch_record(spec=spec, run=run, shard=shard)
        OLD_RUN._install_prelaunch(
            args.evidence_root,
            records={
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
            },
            wrapper=wrapper,
            ctest=ctest,
            raw_discovery=raw_discovery,
        )
        terminal, stdout, stderr = OLD_RUN.execute_process(
            spec, private_root, prelaunch["record_sha256"]
        )
        BASE.install_bytes(args.evidence_root, "raw/stdout.bin", stdout)
        BASE.install_bytes(args.evidence_root, "raw/stderr.bin", stderr)
        BASE.install_json(args.evidence_root, "terminal.json", terminal)
        process = terminal["process"]
        if (
            terminal["class"] != "exited"
            or terminal["exit_code"] not in {0, 8}
            or terminal["signal"] is not None
            or process["watchdog_fired"]
            or not process["direct_child_reaped"]
            or process["live_non_zombie_pids_after_cleanup"] != []
        ):
            raise R4Error("R4 CTest process did not close as an eligible exited group")
        if not junit_path.is_file() or junit_path.is_symlink():
            raise R4Error("R4 CTest process produced no regular JUnit file")
        raw_junit = junit_path.read_bytes()
        BASE.install_bytes(args.evidence_root, "raw/junit.xml", raw_junit)
        junit = M2.parse_junit(raw_junit, terminal)
        BASE.install_json(args.evidence_root, "junit.json", junit)
        cases = M2.build_case_records(spec=spec, terminal=terminal, junit=junit)
        for ordinal, case in enumerate(cases):
            BASE.install_json(args.evidence_root, OLD_STORE.case_path(ordinal), case)
        post, retained = R3.capture_post(
            source_root=source_root, source=source, wrapper=wrapper, junit=junit
        )
        for source_path, payload in retained.items():
            BASE.install_bytes(
                args.evidence_root, OLD_STORE.generated_path(source_path), payload
            )
        BASE.install_json(args.evidence_root, "post.json", post)
        projection = result_projection(junit, post)
        BASE.install_json(args.evidence_root, "projection.json", projection)
        completion = R3.install_completion(args.evidence_root)
        validate_complete_evidence(args.evidence_root)
        BASE.validate_live_readonly_tree(args.evidence_root)
    print(
        "LEAN_U2_M2_R4_RUN|"
        f"cases={projection['credits']['official_cases']}|"
        f"passes={projection['credits']['official_passes']}|"
        f"failures={projection['credits']['official_failures']}|"
        f"completion={completion['record_sha256']}|retained=67|metadata_only=56|"
        "parent_complete=false|provider=false|axeyum=0|pairs=0|parity=0"
    )


def validate_offline_contract() -> dict[str, Any]:
    validate_history()
    contract = M2.validate_offline_contract()
    spec = build_spec(
        implementation_revision="0" * 40,
        source_root=Path("/r4/source"),
        toolchain_root=Path("/r4/toolchain"),
        harness_build=Path("/r4/harness"),
        junit_path=Path("/r4/attempt/test-results.xml"),
    )
    if validate_spec(spec):
        raise R4Error("R4 offline spec drift")
    if resource_envelope()["memory_limit"]["value"] != MEMORY_LIMIT_BYTES:
        raise R4Error("R4 16 GiB resource envelope drift")
    if render_environment_wrapper(Path("/r4/source"), Path("/r4/toolchain")) != _R3_RENDER_WRAPPER(
        Path("/r4/source"), Path("/r4/toolchain")
    ):
        raise R4Error("R4 changed the accepted stack wrapper")
    if len(M2.selected_contract()["cases"]) != 64 or len(R3.declared_generated_paths()) != 124:
        raise R4Error("R4 shard or generated-path count drift")
    return {
        "cases": contract["case_count"],
        "generated": len(R3.declared_generated_paths()),
        "memory_limit_bytes": MEMORY_LIMIT_BYTES,
        "selected_processes": 0,
        "outcomes": 0,
        "parity": 0,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("offline-check")
    stack = commands.add_parser("probe-stack")
    stack.add_argument("--toolchain-root", type=Path, default=DEFAULT_TOOLCHAIN_ROOT)
    fanout = commands.add_parser("probe-fanout")
    fanout.add_argument("--toolchain-root", type=Path, default=DEFAULT_TOOLCHAIN_ROOT)
    run = commands.add_parser("run-r4")
    run.add_argument("--implementation-revision", required=True)
    run.add_argument("--fanout-record-sha256", required=True)
    run.add_argument("--source-repo", type=Path, default=DEFAULT_SOURCE_REPO)
    run.add_argument("--toolchain-root", type=Path, default=DEFAULT_TOOLCHAIN_ROOT)
    run.add_argument("--work-root", type=Path, required=True)
    run.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    validate = commands.add_parser("validate")
    validate.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    incomplete = commands.add_parser("validate-incomplete")
    incomplete.add_argument(
        "--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT
    )
    args = parser.parse_args()
    try:
        if args.command == "offline-check":
            summary = validate_offline_contract()
            print(
                "LEAN_U2_M2_R4|"
                f"cases={summary['cases']}|generated={summary['generated']}|"
                f"memory={MEMORY_LIMIT_BYTES}|selected_processes=0|"
                "outcomes=0|pairs=0|parity=0"
            )
        elif args.command == "probe-stack":
            result = probe_stack_environment(args.toolchain_root)
            print(
                "LEAN_U2_M2_R4_STACK_PROBE|"
                f"source={result['source_sha256']}|exit=0|value={STACK_SIZE_KB}|"
                "selected_case=false"
            )
        elif args.command == "probe-fanout":
            result = probe_fanout(args.toolchain_root)
            print(json.dumps(result, sort_keys=True, separators=(",", ":")))
        elif args.command == "run-r4":
            run_r4(args)
        elif args.command == "validate":
            completion = validate_complete_evidence(args.evidence_root)
            print(
                "LEAN_U2_M2_R4_EVIDENCE_VALID|"
                f"completion={completion['record_sha256']}|cases=64|"
                "parent_complete=false|parity=0"
            )
        elif args.command == "validate-incomplete":
            result = validate_incomplete_evidence(args.evidence_root)
            print(
                "LEAN_U2_M2_R4_INCOMPLETE_VALID|"
                f"terminal={result['terminal']['record_sha256']}|"
                f"class={result['terminal']['class']}|files={result['files']}|"
                f"bytes={result['bytes']}|outcomes=0|parity=0"
            )
        else:  # pragma: no cover
            raise AssertionError(args.command)
    except (
        BASE.U2ExecutionError,
        BASE.STORE.CheckpointConflict,
        M2.M2ContractError,
        OLD_RUN.M2RunError,
        OLD_STORE.M2StoreError,
        R3.R3Error,
        R4Error,
    ) as error:
        print(f"LEAN_U2_M2_R4_ERROR|{error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
