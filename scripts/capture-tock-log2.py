#!/usr/bin/env python3
"""Run ADR-0328's authenticated two-root Tock log2 LLVM capture."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence


REPO = Path(__file__).resolve().parents[1]
DEFAULT_REGISTRATION = (
    REPO / "bench-results/verify-tock-log2-20260721/capture-v1-registration.json"
)
DEFAULT_TOCK_REPO = REPO / "references/tock"
DEFAULT_OUTPUT = REPO / "target/tock-log2-20260721/capture-v1"
DEFAULT_ADMITTER = REPO / "target/debug/axeyum-llvm-scalar-admit"
REGISTRATION_SCHEMA = "axeyum.tock-log2-capture-v1-registration.v1"
RESULT_SCHEMA = "axeyum.tock-log2-capture-v1-result.v1"
AMBIENT_RUSTFLAGS = (
    "RUSTFLAGS",
    "CARGO_BUILD_RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS",
)
EXPECTED_ENVIRONMENT = [
    ["CARGO_BUILD_JOBS", "1"],
    ["CARGO_HOME", "/home/mjbommar/.cargo"],
    ["CARGO_INCREMENTAL", "0"],
    ["CARGO_PROFILE_RELEASE_DEBUG", "0"],
    ["CARGO_TARGET_DIR", "/axeyum-vroot/target"],
    ["HOME", "/home/mjbommar"],
    ["LANG", "C.UTF-8"],
    ["LC_ALL", "C.UTF-8"],
    [
        "PATH",
        "/home/mjbommar/.rustup/toolchains/"
        "nightly-2026-04-21-x86_64-unknown-linux-gnu/bin:/usr/bin:/bin",
    ],
    [
        "RUSTC",
        "/home/mjbommar/.rustup/toolchains/"
        "nightly-2026-04-21-x86_64-unknown-linux-gnu/bin/rustc",
    ],
    ["RUSTUP_HOME", "/home/mjbommar/.rustup"],
    ["SOURCE_DATE_EPOCH", "1784602213"],
]
EXPECTED_BUILD_ARGS = [
    "rustc",
    "-p",
    "kernel",
    "--lib",
    "--release",
    "--locked",
    "--offline",
    "--",
    "-Ccodegen-units=1",
    "-Clink-dead-code",
    "--emit=llvm-ir",
]
EXPECTED_METADATA_ARGS = [
    "metadata",
    "--locked",
    "--offline",
    "--format-version",
    "1",
]
EXPECTED_MEMORY_MAX = 4 * 1024 * 1024 * 1024
EXPECTED_MEMORY_HIGH = 2500 * 1024 * 1024
EXPECTED_SWAP_MAX = 512 * 1024 * 1024
EXPECTED_RESOURCE_SCOPE = {
    "memory_high_bytes": EXPECTED_MEMORY_HIGH,
    "memory_max_bytes": EXPECTED_MEMORY_MAX,
    "swap_max_bytes": EXPECTED_SWAP_MAX,
}
EXPECTED_TOOLS = {
    "bwrap",
    "cargo",
    "dpkg_query",
    "git",
    "gnu_time",
    "llvm_as",
    "llvm_dis",
    "llvm_extract",
    "rustc",
}
EXPECTED_BWRAP_PROBE = [
    "--die-with-parent",
    "--new-session",
    "--unshare-all",
    "--ro-bind",
    "/",
    "/",
    "--dev-bind",
    "/dev",
    "/dev",
    "--proc",
    "/proc",
]
EXPECTED_BWRAP_ROOT = [
    "--die-with-parent",
    "--new-session",
    "--unshare-all",
    "--tmpfs",
    "/",
    "--dir",
    "/usr",
    "--ro-bind",
    "/usr",
    "/usr",
    "--symlink",
    "usr/bin",
    "/bin",
    "--symlink",
    "usr/sbin",
    "/sbin",
    "--symlink",
    "usr/lib",
    "/lib",
    "--symlink",
    "usr/lib64",
    "/lib64",
    "--dir",
    "/etc",
    "--ro-bind",
    "/etc",
    "/etc",
    "--dir",
    "/home",
    "--dir",
    "/home/mjbommar",
    "--ro-bind",
    "/home/mjbommar/.cargo",
    "/home/mjbommar/.cargo",
    "--ro-bind",
    "/home/mjbommar/.rustup",
    "/home/mjbommar/.rustup",
    "--dir",
    "/dev",
    "--dev-bind",
    "/dev",
    "/dev",
    "--dir",
    "/proc",
    "--proc",
    "/proc",
    "--dir",
    "/tmp",
    "--tmpfs",
    "/tmp",
    "--dir",
    "/axeyum-vroot",
]
ADMISSION_KEYS = {
    "stage",
    "kind",
    "function",
    "parameter_widths",
    "return_width",
    "blocks",
    "phis",
    "instructions",
    "canonical_bytes",
}
MODULE_ID = re.compile(br"^; ModuleID = '[^'\r\n]*'\r?\n$")


@dataclass
class CaptureError(Exception):
    stage: str
    kind: str
    detail: str

    def __str__(self) -> str:
        return f"{self.stage}/{self.kind}: {self.detail}"


def fail(stage: str, kind: str, detail: str) -> None:
    raise CaptureError(stage, kind, detail)


def require(condition: bool, stage: str, kind: str, detail: str) -> None:
    if not condition:
        fail(stage, kind, detail)


def require_string(value: Any, where: str) -> str:
    require(isinstance(value, str) and bool(value), "registration", "shape", where)
    return value


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        fail("registration", "decode", f"{path}: {error}")
    require(isinstance(value, dict), "registration", "shape", str(path))
    return value


def command(
    argv: Sequence[str],
    *,
    stage: str,
    kind: str,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        list(argv),
        cwd=cwd,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip() or f"exit {result.returncode}"
        fail(stage, kind, detail)
    return result


def validate_file(path: Path, expected_hash: str, stage: str, kind: str) -> None:
    require(path.is_file(), stage, f"missing_{kind}", str(path))
    require(sha256_file(path) == expected_hash, stage, f"{kind}_hash", str(path))


def tool_report(entry: dict[str, Any], name: str) -> dict[str, str]:
    path = Path(require_string(entry.get("path"), f"tools.{name}.path"))
    digest = require_string(entry.get("sha256"), f"tools.{name}.sha256")
    validate_file(path, digest, "tool", name)
    version_args = entry.get("version_args")
    require(
        isinstance(version_args, list)
        and all(isinstance(value, str) for value in version_args),
        "registration",
        "shape",
        f"tools.{name}.version_args",
    )
    result = command([str(path), *version_args], stage="tool", kind=f"{name}_version")
    version = (result.stdout or result.stderr).strip().splitlines()[0]
    require(
        version == entry.get("version"),
        "tool",
        f"{name}_version",
        version,
    )
    return {"path": str(path), "sha256": digest, "version": version}


def validate_registration(registration: dict[str, Any]) -> None:
    require(
        registration.get("schema") == REGISTRATION_SCHEMA,
        "registration",
        "schema",
        str(registration.get("schema")),
    )
    upstream = registration.get("upstream")
    require(isinstance(upstream, dict), "registration", "shape", "upstream")
    require(
        upstream.get("commit") == "ac5d597d22fbf3b03ef2169a577bac246ef65ffb"
        and upstream.get("tree") == "5243357a7034d3a5fa68487ea839a25e573a25ef",
        "registration",
        "upstream",
        str(upstream),
    )
    require(
        registration.get("environment") == EXPECTED_ENVIRONMENT,
        "registration",
        "environment",
        str(registration.get("environment")),
    )
    require(
        registration.get("build_args") == EXPECTED_BUILD_ARGS
        and registration.get("metadata_args") == EXPECTED_METADATA_ARGS,
        "registration",
        "build_args",
        "command drift",
    )
    require(
        registration.get("resource_scope") == EXPECTED_RESOURCE_SCOPE,
        "registration",
        "resource_scope",
        str(registration.get("resource_scope")),
    )
    tools = registration.get("tools")
    require(
        isinstance(tools, dict) and set(tools) == EXPECTED_TOOLS,
        "registration",
        "tools",
        str(sorted(tools) if isinstance(tools, dict) else tools),
    )
    namespace = registration.get("namespace")
    require(isinstance(namespace, dict), "registration", "shape", "namespace")
    require(
        namespace.get("probe_argv") == EXPECTED_BWRAP_PROBE
        and namespace.get("root_argv") == EXPECTED_BWRAP_ROOT
        and namespace.get("source") == "/axeyum-vroot/source"
        and namespace.get("target") == "/axeyum-vroot/target"
        and namespace.get("cwd") == "/axeyum-vroot/source",
        "registration",
        "namespace",
        str(namespace),
    )
    for field in ("critical_files", "producer_files", "targets"):
        rows = registration.get(field)
        require(isinstance(rows, list) and rows, "registration", "shape", field)
    producer_paths = [entry.get("path") for entry in registration["producer_files"]]
    require(
        producer_paths == sorted(set(producer_paths)),
        "registration",
        "producer_order",
        str(producer_paths),
    )
    for entry in registration["producer_files"]:
        require(isinstance(entry, dict), "registration", "shape", "producer")
        path = REPO / require_string(entry.get("path"), "producer.path")
        validate_file(path, require_string(entry.get("sha256"), "producer.sha256"), "registration", "producer")
    admitter = registration.get("admitter")
    require(isinstance(admitter, dict), "registration", "shape", "admitter")
    admitter_source = REPO / require_string(admitter.get("source"), "admitter.source")
    validate_file(
        admitter_source,
        require_string(admitter.get("source_sha256"), "admitter.source_sha256"),
        "registration",
        "admitter_source",
    )
    require_string(admitter.get("path"), "admitter.path")
    require_string(admitter.get("sha256"), "admitter.sha256")
    target_names = [entry.get("name") for entry in registration["targets"]]
    require(
        target_names == ["log_base_two", "log_base_two_u64"],
        "registration",
        "targets",
        str(target_names),
    )


def validate_source_repo(source_repo: Path, registration: dict[str, Any]) -> None:
    git = registration["tools"]["git"]
    git_path = Path(git["path"])
    status = command(
        [str(git_path), "status", "--porcelain"],
        stage="source",
        kind="git_status",
        cwd=source_repo,
    )
    require(not status.stdout.strip(), "source", "dirty", status.stdout.strip())
    commit = registration["upstream"]["commit"]
    actual_commit = command(
        [str(git_path), "rev-parse", commit], stage="source", kind="commit", cwd=source_repo
    ).stdout.strip()
    actual_tree = command(
        [str(git_path), "rev-parse", f"{commit}^{{tree}}"],
        stage="source",
        kind="tree",
        cwd=source_repo,
    ).stdout.strip()
    require(actual_commit == commit, "source", "commit", actual_commit)
    require(actual_tree == registration["upstream"]["tree"], "source", "tree", actual_tree)


def safe_extract(archive: Path, destination: Path) -> None:
    with tarfile.open(archive, "r:") as stream:
        for member in stream.getmembers():
            path = Path(member.name)
            require(
                not path.is_absolute() and ".." not in path.parts,
                "source",
                "archive_traversal",
                member.name,
            )
        try:
            stream.extractall(destination, filter="data")
        except (tarfile.TarError, OSError) as error:
            fail("source", "archive_extract", str(error))


def validate_materialized(root: Path, registration: dict[str, Any]) -> None:
    for entry in registration["critical_files"]:
        require(isinstance(entry, dict), "registration", "shape", "critical file")
        relative = Path(require_string(entry.get("path"), "critical.path"))
        require(
            not relative.is_absolute() and ".." not in relative.parts,
            "registration",
            "critical_path",
            str(relative),
        )
        validate_file(
            root / relative,
            require_string(entry.get("sha256"), "critical.sha256"),
            "source",
            "critical",
        )


def materialize(source_repo: Path, root: Path, registration: dict[str, Any]) -> None:
    root.mkdir()
    archive = root.parent / f"{root.name}.tar"
    git = registration["tools"]["git"]["path"]
    command(
        [git, "archive", "--format=tar", "--output", str(archive), registration["upstream"]["commit"]],
        stage="source",
        kind="git_archive",
        cwd=source_repo,
    )
    try:
        safe_extract(archive, root)
    finally:
        archive.unlink(missing_ok=True)
    validate_materialized(root, registration)


def reject_ambient_flags(environment: dict[str, str]) -> None:
    present = [name for name in AMBIENT_RUSTFLAGS if name in environment]
    require(not present, "build", "ambient_rustflags", ",".join(present))


def validate_distinct_roots(roots: Sequence[Path]) -> None:
    resolved = [path.resolve() for path in roots]
    require(
        len(resolved) == len(set(resolved)),
        "build",
        "physical_root_alias",
        str(resolved),
    )


def parse_cgroup_limit(value: str, name: str) -> int:
    require(value != "max", "resource", f"{name}_unbounded", value)
    try:
        parsed = int(value)
    except ValueError:
        fail("resource", f"{name}_parse", value)
    require(parsed >= 0, "resource", f"{name}_parse", value)
    return parsed


def parse_memory_events(text: str) -> dict[str, int]:
    events: dict[str, int] = {}
    for line in text.splitlines():
        fields = line.split()
        require(len(fields) == 2, "resource", "memory_events", line)
        name, value = fields
        require(name not in events, "resource", "memory_events", f"duplicate {name}")
        try:
            events[name] = int(value)
        except ValueError:
            fail("resource", "memory_events", line)
    for name in ("oom", "oom_kill", "oom_group_kill"):
        require(name in events, "resource", "memory_events", f"missing {name}")
    return events


def current_cgroup(
    proc_cgroup: Path = Path("/proc/self/cgroup"),
    cgroup_root: Path = Path("/sys/fs/cgroup"),
) -> Path:
    try:
        lines = proc_cgroup.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as error:
        fail("resource", "cgroup", str(error))
    unified = [line.split("::", 1)[1] for line in lines if line.startswith("0::")]
    require(len(unified) == 1, "resource", "cgroup", str(lines))
    relative = Path(unified[0].lstrip("/"))
    require(".." not in relative.parts, "resource", "cgroup", unified[0])
    root = cgroup_root.resolve()
    path = (root / relative).resolve()
    require(path.is_relative_to(root), "resource", "cgroup", str(path))
    return path


def resource_snapshot(
    proc_cgroup: Path = Path("/proc/self/cgroup"),
    cgroup_root: Path = Path("/sys/fs/cgroup"),
) -> dict[str, Any]:
    path = current_cgroup(proc_cgroup, cgroup_root)
    try:
        memory_high = parse_cgroup_limit(
            (path / "memory.high").read_text(encoding="utf-8").strip(),
            "memory_high",
        )
        memory_max = parse_cgroup_limit(
            (path / "memory.max").read_text(encoding="utf-8").strip(), "memory_max"
        )
        swap_max = parse_cgroup_limit(
            (path / "memory.swap.max").read_text(encoding="utf-8").strip(),
            "swap_max",
        )
        events = parse_memory_events(
            (path / "memory.events").read_text(encoding="utf-8")
        )
    except (OSError, UnicodeError) as error:
        fail("resource", "cgroup", str(error))
    require(
        memory_high == EXPECTED_MEMORY_HIGH,
        "resource",
        "memory_high",
        str(memory_high),
    )
    require(
        memory_max == EXPECTED_MEMORY_MAX,
        "resource",
        "memory_max",
        str(memory_max),
    )
    require(
        swap_max == EXPECTED_SWAP_MAX,
        "resource",
        "swap_max",
        str(swap_max),
    )
    return {
        "cgroup": str(path),
        "memory_high_bytes": memory_high,
        "memory_max_bytes": memory_max,
        "swap_max_bytes": swap_max,
        "events": events,
    }


def resource_delta(before: dict[str, Any], after: dict[str, Any]) -> dict[str, int]:
    require(
        before["cgroup"] == after["cgroup"],
        "resource",
        "cgroup_drift",
        str([before["cgroup"], after["cgroup"]]),
    )
    deltas = {
        name: after["events"][name] - before["events"][name]
        for name in ("oom", "oom_kill", "oom_group_kill")
    }
    require(
        all(value == 0 for value in deltas.values()),
        "resource",
        "oom_delta",
        str(deltas),
    )
    return deltas


def bwrap_command(
    registration: dict[str, Any], source: Path, target: Path, child: Sequence[str]
) -> list[str]:
    bwrap = registration["tools"]["bwrap"]["path"]
    command_line = [bwrap, *EXPECTED_BWRAP_ROOT]
    command_line.extend(["--ro-bind", str(source), "/axeyum-vroot/source"])
    command_line.extend(["--bind", str(target), "/axeyum-vroot/target"])
    command_line.extend(["--chdir", "/axeyum-vroot/source", "--clearenv"])
    for name, value in EXPECTED_ENVIRONMENT:
        command_line.extend(["--setenv", name, value])
    command_line.extend(["--", *child])
    return command_line


def probe_namespace(registration: dict[str, Any]) -> None:
    bwrap = registration["tools"]["bwrap"]["path"]
    command(
        [bwrap, *EXPECTED_BWRAP_PROBE, "--", "/usr/bin/true"],
        stage="namespace",
        kind="probe",
    )


def validate_cache(registration: dict[str, Any], source: Path, target: Path) -> None:
    cargo = registration["tools"]["cargo"]["path"]
    result = command(
        bwrap_command(registration, source, target, [cargo, *EXPECTED_METADATA_ARGS]),
        stage="cache",
        kind="offline_metadata",
    )
    try:
        metadata = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        fail("cache", "metadata_json", str(error))
    require(metadata.get("workspace_root") == "/axeyum-vroot/source", "cache", "workspace_root", str(metadata.get("workspace_root")))
    packages = [package.get("name") for package in metadata.get("packages", [])]
    require("kernel" in packages, "cache", "kernel_package", str(packages))


def parse_time_report(path: Path) -> int:
    text = path.read_text(encoding="utf-8")
    match = re.search(r"Maximum resident set size \(kbytes\): (\d+)", text)
    require(match is not None, "build", "time_report", text)
    return int(match.group(1))


def build_kernel(registration: dict[str, Any], source: Path, target: Path) -> tuple[Path, dict[str, int]]:
    cargo = registration["tools"]["cargo"]["path"]
    time_binary = registration["tools"]["gnu_time"]["path"]
    timing = "/axeyum-vroot/target/build.time"
    child = [time_binary, "-v", "-o", timing, cargo, *EXPECTED_BUILD_ARGS]
    started = time.monotonic_ns()
    command(
        bwrap_command(registration, source, target, child),
        stage="build",
        kind="cargo_rustc",
    )
    wall_ms = (time.monotonic_ns() - started) // 1_000_000
    modules = sorted((target / "release/deps").glob("kernel-*.ll"))
    require(len(modules) == 1, "build", "module_count", f"found {len(modules)}")
    return modules[0], {
        "wall_ms": wall_ms,
        "peak_rss_kib": parse_time_report(target / "build.time"),
    }


def reject_host_tokens(module: bytes, roots: Sequence[Path]) -> dict[str, int]:
    for root in roots:
        token = str(root.resolve()).encode()
        require(token not in module, "identity", "host_path", str(root))
    return {
        "virtual_source_occurrences": module.count(b"/axeyum-vroot/source"),
        "virtual_target_occurrences": module.count(b"/axeyum-vroot/target"),
    }


def validate_module_identity(
    module_bytes: Sequence[bytes], build_rows: Sequence[dict[str, Any]]
) -> bytes:
    require(len(module_bytes) == 2, "identity", "module_count", str(len(module_bytes)))
    require(
        len(module_bytes[0]) == len(module_bytes[1]),
        "identity",
        "module_size",
        str([len(data) for data in module_bytes]),
    )
    require(
        module_bytes[0] == module_bytes[1],
        "identity",
        "module_hash",
        str([sha256_bytes(data) for data in module_bytes]),
    )
    require(len(build_rows) == 2, "identity", "build_count", str(len(build_rows)))
    require(
        build_rows[0]["virtual_source_occurrences"]
        == build_rows[1]["virtual_source_occurrences"]
        and build_rows[0]["virtual_target_occurrences"]
        == build_rows[1]["virtual_target_occurrences"],
        "identity",
        "virtual_path_counts",
        str(build_rows),
    )
    return module_bytes[0]


def discover_target(module: bytes, entry: dict[str, Any]) -> dict[str, Any]:
    comment = f"; kernel::utilities::math::{entry['name']}".encode()
    lines = module.splitlines()
    matches = [index for index, line in enumerate(lines) if line == comment]
    require(matches and len(matches) == 1, "symbol", "comment_count", f"{entry['name']}={len(matches)}")
    definition = None
    for line in lines[matches[0] + 1 :]:
        if line.startswith(b"; kernel::utilities::math::"):
            break
        if line.startswith(b"define "):
            definition = line
            break
    require(definition is not None, "symbol", "definition", entry["name"])
    match = re.match(br"^define\s+.*\bi(\d+)\s+@([^\s(]+)\(([^)]*)\)", definition)
    require(match is not None, "symbol", "signature", definition.decode(errors="replace"))
    return_width = int(match.group(1))
    args = match.group(3).split(b",") if match.group(3).strip() else []
    parameter_widths: list[int] = []
    for arg in args:
        width = re.match(br"\s*i(\d+)\b", arg)
        require(width is not None, "symbol", "parameter", arg.decode(errors="replace"))
        parameter_widths.append(int(width.group(1)))
    symbol = match.group(2).decode()
    require(return_width == entry["return_width"], "symbol", "return_width", str(return_width))
    require(parameter_widths == entry["parameter_widths"], "symbol", "parameter_widths", str(parameter_widths))
    definitions = re.findall(br"^define\s+[^\r\n]*@" + re.escape(match.group(2)) + br"\(", module, re.M)
    require(len(definitions) == 1, "symbol", "definition_count", f"{symbol}={len(definitions)}")
    return {
        "name": entry["name"],
        "symbol": symbol,
        "parameter_widths": parameter_widths,
        "return_width": return_width,
    }


def moduleid_agnostic(data: bytes) -> bytes:
    lines = data.splitlines(keepends=True)
    matches = [index for index, line in enumerate(lines) if MODULE_ID.fullmatch(line)]
    require(matches == [0], "extract", "module_id", str(matches))
    return b"".join(lines[1:])


def parse_admission(stdout: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for line in stdout.splitlines():
        require("=" in line, "admission", "output", line)
        name, value = line.split("=", 1)
        require(name not in values, "admission", "output", f"duplicate {name}")
        values[name] = value
    require(set(values) == ADMISSION_KEYS, "admission", "output", str(sorted(values)))
    require(values["stage"] == "accepted" and values["kind"] == "straight_line_scalar", "admission", "declined", stdout)
    return values


def identity_projection(result: dict[str, Any]) -> dict[str, Any]:
    projected = json.loads(json.dumps(result))
    projected.pop("observations", None)
    projected.pop("identity_sha256", None)
    return projected


def run_capture(args: argparse.Namespace) -> dict[str, Any]:
    registration = read_json(args.registration.resolve())
    validate_registration(registration)
    reject_ambient_flags(dict(os.environ))
    source_repo = args.tock_repo.resolve()
    validate_source_repo(source_repo, registration)
    output = args.output.resolve()
    target_root = (REPO / "target").resolve()
    require(output.is_relative_to(target_root), "output", "unsafe_path", str(output))
    require(not output.exists(), "output", "exists", str(output))
    output.parent.mkdir(parents=True, exist_ok=True)
    partial = output.with_name(f".{output.name}.partial-{os.getpid()}")
    require(not partial.exists(), "output", "partial_exists", str(partial))

    tools = {name: tool_report(entry, name) for name, entry in registration["tools"].items()}
    package = command(
        [registration["tools"]["dpkg_query"]["path"], "-W", "-f=${Version}", "llvm-22"],
        stage="tool",
        kind="llvm_package",
    ).stdout
    require(package == registration["llvm_package_version"], "tool", "llvm_package", package)
    validate_file(args.admitter.resolve(), registration["admitter"]["sha256"], "admission", "binary")
    probe_namespace(registration)
    resource_before = resource_snapshot()

    partial.mkdir()
    try:
        with tempfile.TemporaryDirectory(prefix="tock-log2-capture-") as raw_temp:
            temporary = Path(raw_temp)
            sources = [temporary / "source-a", temporary / "source-b"]
            targets = [temporary / "target-a", temporary / "target-b"]
            cache_target = temporary / "cache-probe-target"
            for path in [*targets, cache_target]:
                path.mkdir()
            validate_distinct_roots([*sources, *targets])
            for source in sources:
                materialize(source_repo, source, registration)
            validate_cache(registration, sources[0], cache_target)

            modules: list[Path] = []
            build_rows: list[dict[str, Any]] = []
            root_tokens = [temporary, *sources, *targets, source_repo]
            for label, source, target in zip(("a", "b"), sources, targets):
                module, timing = build_kernel(registration, source, target)
                data = module.read_bytes()
                paths = reject_host_tokens(data, root_tokens)
                row = {
                    "root": label,
                    "module_bytes": len(data),
                    "module_sha256": sha256_bytes(data),
                    **paths,
                    **timing,
                }
                modules.append(module)
                build_rows.append(row)
            first = validate_module_identity(
                [module.read_bytes() for module in modules], build_rows
            )
            command([registration["tools"]["llvm_as"]["path"], str(modules[0]), "-o", "/dev/null"], stage="llvm", kind="module_assemble")

            selected: list[dict[str, Any]] = []
            extracted_root = temporary / "extracted"
            extracted_root.mkdir()
            canonical_root = partial / "canonical"
            canonical_root.mkdir()
            for target_entry in registration["targets"]:
                discovered = [discover_target(module.read_bytes(), target_entry) for module in modules]
                require(discovered[0] == discovered[1], "symbol", "root_drift", str(discovered))
                symbol = discovered[0]["symbol"]
                extracted: list[bytes] = []
                for index, module in enumerate(modules):
                    path = extracted_root / f"{target_entry['name']}-{index}.ll"
                    command(
                        [registration["tools"]["llvm_extract"]["path"], "-S", "--func", symbol, str(module), "-o", str(path)],
                        stage="extract",
                        kind="llvm_extract",
                    )
                    command([registration["tools"]["llvm_as"]["path"], str(path), "-o", "/dev/null"], stage="llvm", kind="extract_assemble")
                    extracted.append(path.read_bytes())
                normalized = [moduleid_agnostic(data) for data in extracted]
                require(normalized[0] == normalized[1], "extract", "root_drift", target_entry["name"])
                canonical = canonical_root / f"{target_entry['name']}.ll"
                admission = command(
                    [str(args.admitter.resolve()), str(extracted_root / f"{target_entry['name']}-0.ll"), str(canonical)],
                    stage="admission",
                    kind="binary",
                )
                admitted = parse_admission(admission.stdout)
                expected_parameters = ",".join(str(width) for width in target_entry["parameter_widths"])
                require(admitted["parameter_widths"] == expected_parameters, "admission", "parameter_widths", str(admitted))
                require(admitted["return_width"] == str(target_entry["return_width"]), "admission", "return_width", str(admitted))
                selected.append(
                    {
                        **discovered[0],
                        "extracted_bytes": len(extracted[0]),
                        "extracted_sha256": sha256_bytes(normalized[0]),
                        "canonical_bytes": canonical.stat().st_size,
                        "canonical_sha256": sha256_file(canonical),
                        "instructions": int(admitted["instructions"]),
                    }
                )

            shutil.copy2(modules[0], partial / "kernel.ll")
            result: dict[str, Any] = {
                "schema": RESULT_SCHEMA,
                "status": "accepted",
                "upstream": registration["upstream"],
                "module": {
                    "bytes": len(first),
                    "sha256": sha256_bytes(first),
                    "virtual_source_occurrences": build_rows[0]["virtual_source_occurrences"],
                    "virtual_target_occurrences": build_rows[0]["virtual_target_occurrences"],
                },
                "targets": selected,
                "tools": tools,
                "admitter_sha256": registration["admitter"]["sha256"],
                "summary": {"builds": 2, "targets": 2, "accepted": 2, "dropped": 0},
                "observations": {
                    "builds": build_rows,
                    "resource": {
                        "before": resource_before,
                        "after": (resource_after := resource_snapshot()),
                        "oom_deltas": resource_delta(resource_before, resource_after),
                    },
                },
            }
            result["identity_sha256"] = sha256_bytes(
                (json.dumps(identity_projection(result), sort_keys=True, separators=(",", ":")) + "\n").encode()
            )
            (partial / "capture-result.json").write_text(
                json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
        partial.rename(output)
        return result
    except BaseException as error:
        shutil.rmtree(partial, ignore_errors=True)
        try:
            resource_delta(resource_before, resource_snapshot())
        except CaptureError as resource_error:
            if resource_error.stage == "resource" and resource_error.kind == "oom_delta":
                raise resource_error from error
        raise


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", type=Path, default=DEFAULT_REGISTRATION)
    parser.add_argument("--tock-repo", type=Path, default=DEFAULT_TOCK_REPO)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--admitter", type=Path, default=DEFAULT_ADMITTER)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        result = run_capture(args)
    except CaptureError as error:
        print(f"stage={error.stage}", file=sys.stderr)
        print(f"kind={error.kind}", file=sys.stderr)
        print(f"detail={error.detail}", file=sys.stderr)
        return 1
    print(f"status={result['status']}")
    print(f"identity_sha256={result['identity_sha256']}")
    print(f"output={args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
