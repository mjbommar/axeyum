#!/usr/bin/env python3
"""Prepare ADR-0330's resolver-corrected, inventoried Tock Cargo cache."""

from __future__ import annotations

import argparse
import importlib.util
import ipaddress
import json
import os
import shutil
import stat
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Sequence


def load_support(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load support module: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


REPO = Path(__file__).resolve().parents[1]
V2 = load_support(
    "tock_cache_v2_support", REPO / "scripts/prepare-tock-log2-cache-v2.py"
)
SUPPORT = V2.SUPPORT
DEFAULT_REGISTRATION = (
    REPO
    / "bench-results/verify-tock-log2-20260721/cache-v3-preparation-registration.json"
)
BASE_REGISTRATION = (
    REPO
    / "bench-results/verify-tock-log2-20260721/cache-v2-preparation-registration.json"
)
BASE_REGISTRATION_IDENTITY = {
    "path": "bench-results/verify-tock-log2-20260721/cache-v2-preparation-registration.json",
    "sha256": "f0852783ec187255248f31501d0c79b4ed54cffd32e003e460c41755c2e1cb48",
}
DEFAULT_TOCK_REPO = REPO / "references/tock"
DEFAULT_OUTPUT = REPO / "target/tock-log2-20260721/cache-v3"
REGISTRATION_SCHEMA = "axeyum.tock-log2-cache-v3-preparation-registration.v1"
RESULT_SCHEMA = "axeyum.tock-log2-cache-v3-preparation-result.v1"
RESOLVER_PATH = Path("/run/systemd/resolve/stub-resolv.conf")
RESOLVER_IDENTITY = {
    "path": str(RESOLVER_PATH),
    "sha256": "acfee52a6a0860bf1ff42bfa79d349f2373a9defc0fb05990489743ae0965ec1",
    "mode": 0o644,
    "size": 939,
}
EXPECTED_TOOLS = {*V2.EXPECTED_TOOLS, "getent"}
EXPECTED_RESOLVER_ROOT_SUFFIX = [
    "--dir",
    "/run",
    "--dir",
    "/run/systemd",
    "--dir",
    "/run/systemd/resolve",
    "--ro-bind",
    str(RESOLVER_PATH),
    str(RESOLVER_PATH),
]
EXPECTED_NETWORK_ROOT = [*V2.EXPECTED_NETWORK_ROOT, *EXPECTED_RESOLVER_ROOT_SUFFIX]
EXPECTED_DNS_ARGS = ["ahostsv4", "github.com"]


CaptureError = SUPPORT.CaptureError
fail = SUPPORT.fail
require = SUPPORT.require
require_string = SUPPORT.require_string
sha256_bytes = SUPPORT.sha256_bytes
command = SUPPORT.command


def read_registration(path: Path) -> dict[str, Any]:
    overlay = SUPPORT.read_json(path)
    require(
        overlay.get("schema") == REGISTRATION_SCHEMA,
        "registration",
        "schema",
        str(overlay.get("schema")),
    )
    require(
        overlay.get("base_registration") == BASE_REGISTRATION_IDENTITY,
        "registration",
        "base_registration",
        str(overlay.get("base_registration")),
    )
    require(
        set(overlay)
        == {
            "schema",
            "base_registration",
            "resolver",
            "dns_args",
            "network_root_suffix",
            "getent",
            "producer_files",
        },
        "registration",
        "overlay_fields",
        str(sorted(overlay)),
    )
    require(
        overlay.get("network_root_suffix") == EXPECTED_RESOLVER_ROOT_SUFFIX,
        "registration",
        "network_root_suffix",
        str(overlay.get("network_root_suffix")),
    )
    SUPPORT.validate_file(
        BASE_REGISTRATION,
        BASE_REGISTRATION_IDENTITY["sha256"],
        "registration",
        "base_registration",
    )
    base = SUPPORT.read_json(BASE_REGISTRATION)
    V2.validate_registration(base)
    producers = overlay.get("producer_files")
    require(isinstance(producers, list) and producers, "registration", "shape", "producer_files")
    getent = overlay.get("getent")
    require(isinstance(getent, dict), "registration", "shape", "getent")
    registration = json.loads(json.dumps(base))
    registration["schema"] = REGISTRATION_SCHEMA
    registration["base_registration"] = BASE_REGISTRATION_IDENTITY
    registration["resolver"] = overlay.get("resolver")
    registration["dns_args"] = overlay.get("dns_args")
    registration["namespace"]["network_root_argv"] = EXPECTED_NETWORK_ROOT
    registration["tools"]["getent"] = getent
    registration["producer_files"] = sorted(
        [*registration["producer_files"], *producers], key=lambda row: row["path"]
    )
    return registration


def validate_registration(registration: dict[str, Any]) -> None:
    require(
        registration.get("schema") == REGISTRATION_SCHEMA,
        "registration",
        "schema",
        str(registration.get("schema")),
    )
    require(
        registration.get("base_registration") == BASE_REGISTRATION_IDENTITY,
        "registration",
        "base_registration",
        str(registration.get("base_registration")),
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
        registration.get("environment") == V2.EXPECTED_ENVIRONMENT,
        "registration",
        "environment",
        "environment drift",
    )
    require(
        registration.get("fetch_args") == V2.EXPECTED_FETCH_ARGS
        and registration.get("metadata_args") == V2.EXPECTED_METADATA_ARGS
        and registration.get("dns_args") == EXPECTED_DNS_ARGS,
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
    require(
        registration.get("resolver") == RESOLVER_IDENTITY,
        "registration",
        "resolver",
        str(registration.get("resolver")),
    )
    namespace = registration.get("namespace")
    require(isinstance(namespace, dict), "registration", "shape", "namespace")
    require(
        namespace.get("network_root_argv") == EXPECTED_NETWORK_ROOT
        and namespace.get("offline_root_argv") == V2.EXPECTED_OFFLINE_ROOT
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


def validate_resolver() -> None:
    try:
        info = RESOLVER_PATH.lstat()
    except OSError as error:
        fail("resolver", "file", str(error))
    require(stat.S_ISREG(info.st_mode), "resolver", "kind", str(RESOLVER_PATH))
    require(
        stat.S_IMODE(info.st_mode) == RESOLVER_IDENTITY["mode"],
        "resolver",
        "mode",
        oct(stat.S_IMODE(info.st_mode)),
    )
    require(
        info.st_size == RESOLVER_IDENTITY["size"],
        "resolver",
        "size",
        str(info.st_size),
    )
    SUPPORT.validate_file(
        RESOLVER_PATH,
        RESOLVER_IDENTITY["sha256"],
        "resolver",
        "file",
    )


def network_namespace_command(
    registration: dict[str, Any],
    *,
    source: Path,
    cache: Path,
    target: Path,
    child: Sequence[str],
) -> list[str]:
    command_line = [registration["tools"]["bwrap"]["path"], *EXPECTED_NETWORK_ROOT]
    command_line.extend(["--ro-bind", str(source), "/axeyum-vroot/source"])
    command_line.extend(["--bind", str(cache), "/axeyum-vroot/cache"])
    command_line.extend(["--bind", str(target), "/axeyum-vroot/target"])
    command_line.extend(["--chdir", "/axeyum-vroot/source", "--clearenv"])
    for name, value in V2.EXPECTED_ENVIRONMENT:
        command_line.extend(["--setenv", name, value])
    command_line.extend(["--", *child])
    return command_line


def parse_dns_output(stdout: str) -> list[str]:
    addresses: set[str] = set()
    for line in stdout.splitlines():
        fields = line.split()
        if not fields:
            continue
        try:
            addresses.add(str(ipaddress.IPv4Address(fields[0])))
        except ipaddress.AddressValueError:
            fail("dns", "output", line)
    require(bool(addresses), "dns", "empty", stdout)
    return sorted(addresses, key=lambda value: int(ipaddress.IPv4Address(value)))


def dns_probe(
    registration: dict[str, Any], source: Path, cache: Path, target: Path
) -> list[str]:
    getent = registration["tools"]["getent"]["path"]
    result = command(
        network_namespace_command(
            registration,
            source=source,
            cache=cache,
            target=target,
            child=[getent, *EXPECTED_DNS_ARGS],
        ),
        stage="dns",
        kind="getent",
    )
    return parse_dns_output(result.stdout)


def run_fetch(
    registration: dict[str, Any], source: Path, cache: Path, target: Path
) -> dict[str, int]:
    cargo = registration["tools"]["cargo"]["path"]
    time_binary = registration["tools"]["gnu_time"]["path"]
    child = [
        time_binary,
        "-v",
        "-o",
        "/axeyum-vroot/target/fetch.time",
        cargo,
        *V2.EXPECTED_FETCH_ARGS,
    ]
    started = time.monotonic_ns()
    command(
        network_namespace_command(
            registration,
            source=source,
            cache=cache,
            target=target,
            child=child,
        ),
        stage="fetch",
        kind="cargo_fetch",
    )
    return {
        "wall_ms": (time.monotonic_ns() - started) // 1_000_000,
        "peak_rss_kib": SUPPORT.parse_time_report(target / "fetch.time"),
    }


def run_preparation(args: argparse.Namespace) -> dict[str, Any]:
    registration = read_registration(args.registration.resolve())
    validate_registration(registration)
    V2.reject_ambient_environment(dict(os.environ))
    validate_resolver()
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
        with tempfile.TemporaryDirectory(prefix="tock-cache-v3-") as raw:
            temporary = Path(raw)
            source = temporary / "source"
            dns_target = temporary / "dns-target"
            network_target = temporary / "network-target"
            offline_target = temporary / "offline-target"
            for path in (dns_target, network_target, offline_target):
                path.mkdir()
            SUPPORT.validate_distinct_roots(
                [source, cache, dns_target, network_target, offline_target]
            )
            SUPPORT.materialize(source_repo, source, registration)
            lock_packages = V2.lock_package_count(source)
            require(
                lock_packages == registration["expected_lock_packages"],
                "source",
                "lock_packages",
                str(lock_packages),
            )
            addresses = dns_probe(registration, source, cache, dns_target)
            fetch_observations = run_fetch(registration, source, cache, network_target)
            inventory_before = V2.inventory_cache(cache)
            probe = V2.offline_probe(registration, source, cache, offline_target)
            inventory_after = V2.inventory_cache(cache)
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
                "resolver": registration["resolver"],
                "summary": {
                    "dns_probes": 1,
                    "fetches": 1,
                    "builds": 0,
                    "captures": 0,
                    "property_queries": 0,
                },
                "tools": tools,
                "observations": {
                    "dns_addresses": addresses,
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
                        V2.identity_projection(result),
                        sort_keys=True,
                        separators=(",", ":"),
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
