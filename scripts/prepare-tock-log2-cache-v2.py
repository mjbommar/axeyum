#!/usr/bin/env python3
"""Prepare ADR-0329's dedicated, inventoried Tock Cargo cache."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import shutil
import stat
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Sequence


def load_support(path: Path):
    spec = importlib.util.spec_from_file_location("tock_capture_v1_support", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load support module: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


REPO = Path(__file__).resolve().parents[1]
SUPPORT = load_support(REPO / "scripts/capture-tock-log2.py")
DEFAULT_REGISTRATION = (
    REPO
    / "bench-results/verify-tock-log2-20260721/cache-v2-preparation-registration.json"
)
DEFAULT_TOCK_REPO = REPO / "references/tock"
DEFAULT_OUTPUT = REPO / "target/tock-log2-20260721/cache-v2"
REGISTRATION_SCHEMA = "axeyum.tock-log2-cache-v2-preparation-registration.v1"
RESULT_SCHEMA = "axeyum.tock-log2-cache-v2-preparation-result.v1"
EXPECTED_TOOLS = {"bwrap", "cargo", "git", "gnu_time", "rustc"}
EXPECTED_ENVIRONMENT = [
    ["CARGO_BUILD_JOBS", "1"],
    ["CARGO_CACHE_AUTO_CLEAN_FREQUENCY", "never"],
    ["CARGO_HOME", "/axeyum-vroot/cache"],
    ["CARGO_INCREMENTAL", "0"],
    ["CARGO_NET_GIT_FETCH_WITH_CLI", "false"],
    ["CARGO_TARGET_DIR", "/axeyum-vroot/target"],
    ["CARGO_TERM_COLOR", "never"],
    ["GIT_CONFIG_GLOBAL", "/dev/null"],
    ["GIT_CONFIG_NOSYSTEM", "1"],
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
EXPECTED_FETCH_ARGS = [
    "fetch",
    "--locked",
    "--manifest-path",
    "/axeyum-vroot/source/Cargo.toml",
]
EXPECTED_METADATA_ARGS = [
    "metadata",
    "--locked",
    "--offline",
    "--manifest-path",
    "/axeyum-vroot/source/Cargo.toml",
    "--format-version",
    "1",
]
COMMON_ROOT = [
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
EXPECTED_NETWORK_ROOT = [*COMMON_ROOT[:3], "--share-net", *COMMON_ROOT[3:]]
EXPECTED_OFFLINE_ROOT = COMMON_ROOT
REJECTED_ENV_NAMES = {
    "ALL_PROXY",
    "CARGO_BUILD_RUSTFLAGS",
    "CARGO_CREDENTIAL_ALIAS",
    "CARGO_ENCODED_RUSTFLAGS",
    "CARGO_HOME",
    "CARGO_TARGET_DIR",
    "GIT_ASKPASS",
    "GIT_CONFIG",
    "GIT_CONFIG_GLOBAL",
    "GIT_CONFIG_SYSTEM",
    "GIT_SSH",
    "GIT_SSH_COMMAND",
    "HTTP_PROXY",
    "HTTPS_PROXY",
    "NO_PROXY",
    "RUSTC",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "RUSTFLAGS",
    "RUSTUP_HOME",
    "SSH_ASKPASS",
    "all_proxy",
    "http_proxy",
    "https_proxy",
    "no_proxy",
}
REJECTED_ENV_PREFIXES = (
    "CARGO_HTTP_",
    "CARGO_NET_",
    "CARGO_REGISTRIES_",
    "CARGO_SOURCE_",
)


CaptureError = SUPPORT.CaptureError
fail = SUPPORT.fail
require = SUPPORT.require
require_string = SUPPORT.require_string
sha256_bytes = SUPPORT.sha256_bytes
sha256_file = SUPPORT.sha256_file
command = SUPPORT.command


def read_registration(path: Path) -> dict[str, Any]:
    return SUPPORT.read_json(path)


def validate_registration(registration: dict[str, Any]) -> None:
    require(
        registration.get("schema") == REGISTRATION_SCHEMA,
        "registration",
        "schema",
        str(registration.get("schema")),
    )
    require(
        registration.get("upstream")
        == {
            "commit": "ac5d597d22fbf3b03ef2169a577bac246ef65ffb",
            "tree": "5243357a7034d3a5fa68487ea839a25e573a25ef",
        },
        "registration",
        "upstream",
        str(registration.get("upstream")),
    )
    require(
        registration.get("environment") == EXPECTED_ENVIRONMENT,
        "registration",
        "environment",
        "environment drift",
    )
    require(
        registration.get("fetch_args") == EXPECTED_FETCH_ARGS
        and registration.get("metadata_args") == EXPECTED_METADATA_ARGS,
        "registration",
        "command",
        "command drift",
    )
    require(
        registration.get("resource_scope") == SUPPORT.EXPECTED_RESOURCE_SCOPE,
        "registration",
        "resource_scope",
        str(registration.get("resource_scope")),
    )
    namespace = registration.get("namespace")
    require(isinstance(namespace, dict), "registration", "shape", "namespace")
    require(
        namespace.get("network_root_argv") == EXPECTED_NETWORK_ROOT
        and namespace.get("offline_root_argv") == EXPECTED_OFFLINE_ROOT
        and namespace.get("source") == "/axeyum-vroot/source"
        and namespace.get("cache") == "/axeyum-vroot/cache"
        and namespace.get("target") == "/axeyum-vroot/target"
        and namespace.get("cwd") == "/axeyum-vroot/source",
        "registration",
        "namespace",
        str(namespace),
    )
    tools = registration.get("tools")
    require(
        isinstance(tools, dict) and set(tools) == EXPECTED_TOOLS,
        "registration",
        "tools",
        str(sorted(tools) if isinstance(tools, dict) else tools),
    )
    for field in ("critical_files", "producer_files"):
        rows = registration.get(field)
        require(isinstance(rows, list) and rows, "registration", "shape", field)
        paths = [row.get("path") for row in rows]
        require(paths == sorted(set(paths)), "registration", f"{field}_order", str(paths))
    for entry in registration["producer_files"]:
        path = REPO / require_string(entry.get("path"), "producer.path")
        SUPPORT.validate_file(
            path,
            require_string(entry.get("sha256"), "producer.sha256"),
            "registration",
            "producer",
        )
    require(
        registration.get("expected_lock_packages") == 169,
        "registration",
        "lock_packages",
        str(registration.get("expected_lock_packages")),
    )


def reject_ambient_environment(environment: dict[str, str]) -> None:
    rejected = sorted(
        name
        for name in environment
        if name in REJECTED_ENV_NAMES
        or any(name.startswith(prefix) for prefix in REJECTED_ENV_PREFIXES)
    )
    require(not rejected, "environment", "ambient_override", ",".join(rejected))


def namespace_command(
    registration: dict[str, Any],
    *,
    network: bool,
    source: Path,
    cache: Path,
    target: Path,
    child: Sequence[str],
) -> list[str]:
    root = EXPECTED_NETWORK_ROOT if network else EXPECTED_OFFLINE_ROOT
    command_line = [registration["tools"]["bwrap"]["path"], *root]
    command_line.extend(["--ro-bind", str(source), "/axeyum-vroot/source"])
    command_line.extend(
        ["--bind" if network else "--ro-bind", str(cache), "/axeyum-vroot/cache"]
    )
    command_line.extend(["--bind", str(target), "/axeyum-vroot/target"])
    command_line.extend(["--chdir", "/axeyum-vroot/source", "--clearenv"])
    for name, value in EXPECTED_ENVIRONMENT:
        command_line.extend(["--setenv", name, value])
    command_line.extend(["--", *child])
    return command_line


def lock_package_count(source: Path) -> int:
    lock = (source / "Cargo.lock").read_text(encoding="utf-8")
    return sum(line == "[[package]]" for line in lock.splitlines())


def inventory_cache(root: Path) -> dict[str, Any]:
    require(root.is_dir() and not root.is_symlink(), "inventory", "root", str(root))
    rows: list[dict[str, Any]] = []
    inodes: dict[tuple[int, int], str] = {}
    counts = {"directories": 0, "files": 0, "symlinks": 0, "bytes": 0}
    for path in sorted(root.rglob("*"), key=lambda value: value.relative_to(root).as_posix()):
        relative = path.relative_to(root).as_posix()
        info = path.lstat()
        mode = stat.S_IMODE(info.st_mode)
        if stat.S_ISDIR(info.st_mode):
            rows.append({"kind": "directory", "mode": mode, "path": relative})
            counts["directories"] += 1
        elif stat.S_ISREG(info.st_mode):
            identity = (info.st_dev, info.st_ino)
            require(
                identity not in inodes,
                "inventory",
                "hardlink",
                f"{inodes.get(identity)}={relative}",
            )
            inodes[identity] = relative
            require(
                not relative.endswith((".part", ".tmp")),
                "inventory",
                "temporary_path",
                relative,
            )
            rows.append(
                {
                    "kind": "file",
                    "mode": mode,
                    "path": relative,
                    "sha256": sha256_file(path),
                    "size": info.st_size,
                }
            )
            counts["files"] += 1
            counts["bytes"] += info.st_size
        elif stat.S_ISLNK(info.st_mode):
            target = os.readlink(path)
            target_path = Path(target)
            require(
                not target_path.is_absolute(),
                "inventory",
                "absolute_symlink",
                f"{relative}={target}",
            )
            resolved = path.resolve(strict=False)
            require(
                resolved.is_relative_to(root.resolve()),
                "inventory",
                "escaping_symlink",
                f"{relative}={target}",
            )
            require(path.exists(), "inventory", "dangling_symlink", relative)
            rows.append(
                {"kind": "symlink", "mode": mode, "path": relative, "target": target}
            )
            counts["symlinks"] += 1
        else:
            fail("inventory", "special_file", relative)
    canonical = (json.dumps(rows, sort_keys=True, separators=(",", ":")) + "\n").encode()
    registry_packages = sum(
        row["kind"] == "directory"
        and len(Path(row["path"]).parts) == 4
        and Path(row["path"]).parts[:2] == ("registry", "src")
        for row in rows
    )
    git_checkouts = sum(
        row["kind"] == "directory"
        and len(Path(row["path"]).parts) == 4
        and Path(row["path"]).parts[:2] == ("git", "checkouts")
        for row in rows
    )
    return {
        "sha256": sha256_bytes(canonical),
        "rows": len(rows),
        **counts,
        "registry_packages": registry_packages,
        "git_checkouts": git_checkouts,
    }


def parse_peak_rss(path: Path) -> int:
    return SUPPORT.parse_time_report(path)


def run_fetch(
    registration: dict[str, Any], source: Path, cache: Path, target: Path, timing: Path
) -> dict[str, int]:
    cargo = registration["tools"]["cargo"]["path"]
    time_binary = registration["tools"]["gnu_time"]["path"]
    timing_virtual = "/axeyum-vroot/target/fetch.time"
    child = [time_binary, "-v", "-o", timing_virtual, cargo, *EXPECTED_FETCH_ARGS]
    started = time.monotonic_ns()
    command(
        namespace_command(
            registration,
            network=True,
            source=source,
            cache=cache,
            target=target,
            child=child,
        ),
        stage="fetch",
        kind="cargo_fetch",
    )
    report = target / "fetch.time"
    shutil.copy2(report, timing)
    return {
        "wall_ms": (time.monotonic_ns() - started) // 1_000_000,
        "peak_rss_kib": parse_peak_rss(report),
    }


def offline_probe(
    registration: dict[str, Any], source: Path, cache: Path, target: Path
) -> dict[str, Any]:
    cargo = registration["tools"]["cargo"]["path"]
    result = command(
        namespace_command(
            registration,
            network=False,
            source=source,
            cache=cache,
            target=target,
            child=[cargo, *EXPECTED_METADATA_ARGS],
        ),
        stage="probe",
        kind="offline_metadata",
    )
    try:
        metadata = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        fail("probe", "metadata_json", str(error))
    require(
        metadata.get("workspace_root") == "/axeyum-vroot/source",
        "probe",
        "workspace_root",
        str(metadata.get("workspace_root")),
    )
    packages = metadata.get("packages")
    require(isinstance(packages, list), "probe", "packages", str(type(packages)))
    names = [package.get("name") for package in packages]
    require("kernel" in names, "probe", "kernel_package", str(names))
    require(
        len(packages) == registration["expected_lock_packages"],
        "probe",
        "package_count",
        str(len(packages)),
    )
    return {"packages": len(packages), "kernel_packages": names.count("kernel")}


def identity_projection(result: dict[str, Any]) -> dict[str, Any]:
    projected = json.loads(json.dumps(result))
    projected.pop("observations", None)
    projected.pop("identity_sha256", None)
    return projected


def run_preparation(args: argparse.Namespace) -> dict[str, Any]:
    registration = read_registration(args.registration.resolve())
    validate_registration(registration)
    reject_ambient_environment(dict(os.environ))
    source_repo = args.tock_repo.resolve()
    SUPPORT.validate_source_repo(source_repo, registration)
    tools = {
        name: SUPPORT.tool_report(entry, name)
        for name, entry in registration["tools"].items()
    }
    output = args.output.resolve()
    target_root = (REPO / "target/tock-log2-20260721").resolve()
    require(output.is_relative_to(target_root), "output", "unsafe_path", str(output))
    require(not output.exists(), "output", "exists", str(output))
    output.parent.mkdir(parents=True, exist_ok=True)
    partial = output.with_name(f".{output.name}.partial-{os.getpid()}")
    require(not partial.exists(), "output", "partial_exists", str(partial))
    resource_before = SUPPORT.resource_snapshot()
    partial.mkdir()
    cache = partial / "cargo-home"
    cache.mkdir()
    try:
        with tempfile.TemporaryDirectory(prefix="tock-cache-v2-") as raw:
            temporary = Path(raw)
            source = temporary / "source"
            network_target = temporary / "network-target"
            offline_target = temporary / "offline-target"
            timing = temporary / "fetch.time"
            network_target.mkdir()
            offline_target.mkdir()
            SUPPORT.validate_distinct_roots(
                [source, cache, network_target, offline_target]
            )
            SUPPORT.materialize(source_repo, source, registration)
            require(
                lock_package_count(source) == registration["expected_lock_packages"],
                "source",
                "lock_packages",
                str(lock_package_count(source)),
            )
            fetch_observations = run_fetch(
                registration, source, cache, network_target, timing
            )
            inventory_before = inventory_cache(cache)
            probe = offline_probe(registration, source, cache, offline_target)
            inventory_after = inventory_cache(cache)
            require(
                inventory_before == inventory_after,
                "inventory",
                "probe_drift",
                str([inventory_before, inventory_after]),
            )
            resource_after = SUPPORT.resource_snapshot()
            oom_deltas = SUPPORT.resource_delta(resource_before, resource_after)
            result: dict[str, Any] = {
                "schema": RESULT_SCHEMA,
                "status": "accepted",
                "upstream": registration["upstream"],
                "inventory": inventory_after,
                "probe": probe,
                "summary": {
                    "fetches": 1,
                    "builds": 0,
                    "captures": 0,
                    "property_queries": 0,
                },
                "tools": tools,
                "observations": {
                    "fetch": fetch_observations,
                    "resource": {
                        "before": resource_before,
                        "after": resource_after,
                        "oom_deltas": oom_deltas,
                    },
                },
            }
            result["identity_sha256"] = sha256_bytes(
                (
                    json.dumps(
                        identity_projection(result), sort_keys=True, separators=(",", ":")
                    )
                    + "\n"
                ).encode()
            )
            (partial / "preparation-result.json").write_text(
                json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
        partial.rename(output)
        return result
    except BaseException as error:
        shutil.rmtree(partial, ignore_errors=True)
        try:
            SUPPORT.resource_delta(resource_before, SUPPORT.resource_snapshot())
        except CaptureError as resource_error:
            if resource_error.stage == "resource" and resource_error.kind == "oom_delta":
                raise resource_error from error
        raise


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", type=Path, default=DEFAULT_REGISTRATION)
    parser.add_argument("--tock-repo", type=Path, default=DEFAULT_TOCK_REPO)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        result = run_preparation(args)
    except CaptureError as error:
        print(f"stage={error.stage}", file=sys.stderr)
        print(f"kind={error.kind}", file=sys.stderr)
        print(f"detail={error.detail}", file=sys.stderr)
        return 1
    print(f"status={result['status']}")
    print(f"identity_sha256={result['identity_sha256']}")
    print(f"inventory_sha256={result['inventory']['sha256']}")
    print(f"output={args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
