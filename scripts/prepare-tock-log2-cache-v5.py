#!/usr/bin/env python3
"""Prepare ADR-0332's structurally authenticated Tock Cargo cache."""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import sys
import tomllib
from pathlib import Path, PurePosixPath
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
V4 = load_support(
    "tock_cache_v4_support", REPO / "scripts/prepare-tock-log2-cache-v4.py"
)
SUPPORT = V4.SUPPORT
V4_VALIDATE_REGISTRATION = V4.validate_registration
DEFAULT_REGISTRATION = (
    REPO
    / "bench-results/verify-tock-log2-20260721/cache-v5-preparation-registration.json"
)
BASE_REGISTRATION = (
    REPO
    / "bench-results/verify-tock-log2-20260721/cache-v4-preparation-registration.json"
)
BASE_REGISTRATION_IDENTITY = {
    "path": "bench-results/verify-tock-log2-20260721/cache-v4-preparation-registration.json",
    "sha256": "f940e75a8cd4b89834b635188441ef31c243b4736e04a256f9cbe33b6d980b0e",
}
DEFAULT_TOCK_REPO = REPO / "references/tock"
DEFAULT_OUTPUT = REPO / "target/tock-log2-20260721/cache-v5"
REGISTRATION_SCHEMA = "axeyum.tock-log2-cache-v5-preparation-registration.v1"
RESULT_SCHEMA = "axeyum.tock-log2-cache-v5-preparation-result.v1"
METADATA_SCHEMA = "axeyum.cargo-metadata-lock-authentication.v1"
HEX_64 = re.compile(r"^[0-9a-f]{64}$")


CaptureError = SUPPORT.CaptureError
fail = SUPPORT.fail
require = SUPPORT.require


def read_registration(path: Path) -> dict[str, Any]:
    overlay = SUPPORT.read_json(path)
    require(
        set(overlay)
        == {"schema", "base_registration", "metadata_schema", "producer_files"},
        "registration",
        "overlay_fields",
        str(sorted(overlay)),
    )
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
        overlay.get("metadata_schema") == METADATA_SCHEMA,
        "registration",
        "metadata_schema",
        str(overlay.get("metadata_schema")),
    )
    SUPPORT.validate_file(
        BASE_REGISTRATION,
        BASE_REGISTRATION_IDENTITY["sha256"],
        "registration",
        "base_registration",
    )
    base = V4.read_registration(BASE_REGISTRATION)
    V4_VALIDATE_REGISTRATION(base)
    producers = overlay.get("producer_files")
    require(isinstance(producers, list) and producers, "registration", "shape", "producer_files")
    registration = json.loads(json.dumps(base))
    registration["schema"] = REGISTRATION_SCHEMA
    registration["base_registration"] = BASE_REGISTRATION_IDENTITY
    registration["metadata_schema"] = METADATA_SCHEMA
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
        registration.get("metadata_schema") == METADATA_SCHEMA,
        "registration",
        "metadata_schema",
        str(registration.get("metadata_schema")),
    )
    inherited = json.loads(json.dumps(registration))
    inherited["schema"] = V4.REGISTRATION_SCHEMA
    inherited["base_registration"] = V4.BASE_REGISTRATION_IDENTITY
    V4_VALIDATE_REGISTRATION(inherited)


def require_text(value: Any, stage: str, kind: str, detail: str) -> str:
    require(isinstance(value, str) and bool(value), stage, kind, detail)
    return value


def lock_packages(source: Path, expected_count: int) -> dict[tuple[str, str, str | None], dict[str, Any]]:
    try:
        lock = tomllib.loads((source / "Cargo.lock").read_text(encoding="utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        fail("probe", "lockfile", str(error))
    packages = lock.get("package")
    require(isinstance(packages, list), "probe", "lockfile", "package array")
    require(len(packages) == expected_count, "probe", "lock_package_count", str(len(packages)))
    rows: dict[tuple[str, str, str | None], dict[str, Any]] = {}
    for package in packages:
        require(isinstance(package, dict), "probe", "lockfile", str(package))
        name = require_text(package.get("name"), "probe", "lock_identity", "name")
        version = require_text(package.get("version"), "probe", "lock_identity", name)
        source_value = package.get("source")
        require(source_value is None or isinstance(source_value, str), "probe", "lock_identity", name)
        key = (name, version, source_value)
        require(key not in rows, "probe", "duplicate_lock_identity", str(key))
        checksum = package.get("checksum")
        if source_value is not None and source_value.startswith("registry+"):
            require(
                isinstance(checksum, str) and HEX_64.fullmatch(checksum) is not None,
                "probe",
                "registry_checksum",
                str(key),
            )
        else:
            require(checksum is None, "probe", "unexpected_checksum", str(key))
        rows[key] = {"checksum": checksum}
    return rows


def structural_probe(
    registration: dict[str, Any], source: Path, cache: Path, target: Path
) -> dict[str, Any]:
    cargo = registration["tools"]["cargo"]["path"]
    result = SUPPORT.command(
        V4.V3.V2.namespace_command(
            registration,
            network=False,
            source=source,
            cache=cache,
            target=target,
            child=[cargo, *V4.V3.V2.EXPECTED_METADATA_ARGS],
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
    locks = lock_packages(source, registration["expected_lock_packages"])
    packages = metadata.get("packages")
    resolve = metadata.get("resolve")
    require(isinstance(packages, list), "probe", "packages", str(type(packages)))
    require(isinstance(resolve, dict), "probe", "resolve", str(type(resolve)))
    nodes = resolve.get("nodes")
    require(isinstance(nodes, list), "probe", "nodes", str(type(nodes)))

    package_by_id: dict[str, dict[str, Any]] = {}
    active_rows: list[dict[str, Any]] = []
    counts = {"external": 0, "path": 0, "registry": 0, "git": 0}
    virtual_root = PurePosixPath("/axeyum-vroot/source")
    for package in packages:
        require(isinstance(package, dict), "probe", "package", str(package))
        package_id = require_text(package.get("id"), "probe", "package_id", "id")
        require(package_id not in package_by_id, "probe", "duplicate_package_id", package_id)
        name = require_text(package.get("name"), "probe", "package_identity", package_id)
        version = require_text(package.get("version"), "probe", "package_identity", package_id)
        source_value = package.get("source")
        require(source_value is None or isinstance(source_value, str), "probe", "package_identity", package_id)
        manifest = require_text(package.get("manifest_path"), "probe", "manifest", package_id)
        key = (name, version, source_value)
        require(key in locks, "probe", "package_not_locked", str(key))
        checksum = locks[key]["checksum"]
        if source_value is None:
            counts["path"] += 1
            virtual_manifest = PurePosixPath(manifest)
            try:
                relative = virtual_manifest.relative_to(virtual_root)
            except ValueError:
                fail("probe", "manifest_escape", manifest)
            require(".." not in relative.parts, "probe", "manifest_escape", manifest)
            physical = source.joinpath(*relative.parts)
            require(physical.is_file(), "probe", "manifest_missing", str(relative))
        else:
            counts["external"] += 1
            if source_value.startswith("registry+"):
                counts["registry"] += 1
            elif source_value.startswith("git+"):
                counts["git"] += 1
            else:
                fail("probe", "package_source", source_value)
        row = {
            "checksum": checksum,
            "id": package_id,
            "manifest_path": manifest,
            "name": name,
            "source": source_value,
            "version": version,
        }
        active_rows.append(row)
        package_by_id[package_id] = package

    node_ids: set[str] = set()
    edges = 0
    for node in nodes:
        require(isinstance(node, dict), "probe", "node", str(node))
        node_id = require_text(node.get("id"), "probe", "node_id", "id")
        require(node_id not in node_ids, "probe", "duplicate_node_id", node_id)
        node_ids.add(node_id)
        dependencies = node.get("dependencies")
        deps = node.get("deps")
        require(isinstance(dependencies, list) and isinstance(deps, list), "probe", "node_edges", node_id)
        for dependency in dependencies:
            require(dependency in package_by_id, "probe", "unknown_dependency", str(dependency))
        for dependency in deps:
            require(isinstance(dependency, dict), "probe", "node_edges", node_id)
            package_ref = dependency.get("pkg")
            require(package_ref in package_by_id, "probe", "unknown_dependency", str(package_ref))
            edges += 1
    require(node_ids == set(package_by_id), "probe", "node_package_set", str([len(node_ids), len(package_by_id)]))

    workspace_members = metadata.get("workspace_members")
    default_members = metadata.get("workspace_default_members")
    require(isinstance(workspace_members, list), "probe", "workspace_members", str(type(workspace_members)))
    require(isinstance(default_members, list), "probe", "default_members", str(type(default_members)))
    workspace_set = set(workspace_members)
    default_set = set(default_members)
    require(len(workspace_set) == len(workspace_members), "probe", "duplicate_workspace_member", str(workspace_members))
    require(workspace_set <= set(package_by_id), "probe", "unknown_workspace_member", str(workspace_set - set(package_by_id)))
    require(default_set <= workspace_set, "probe", "default_not_workspace", str(default_set - workspace_set))
    kernels = [row["id"] for row in active_rows if row["name"] == "kernel"]
    require(len(kernels) == 1, "probe", "kernel_package", str(kernels))
    require(kernels[0] in workspace_set, "probe", "kernel_workspace", kernels[0])

    active_rows.sort(key=lambda row: row["id"])
    canonical = (json.dumps(active_rows, sort_keys=True, separators=(",", ":")) + "\n").encode()
    return {
        "schema": METADATA_SCHEMA,
        "active_resolution_sha256": SUPPORT.sha256_bytes(canonical),
        "packages": len(active_rows),
        "nodes": len(nodes),
        "edges": edges,
        "workspace_members": len(workspace_members),
        "default_members": len(default_members),
        **counts,
        "kernel_packages": 1,
        "lock_packages": len(locks),
    }


def run_preparation(args: argparse.Namespace) -> dict[str, Any]:
    registration = read_registration(args.registration.resolve())
    validate_registration(registration)
    V4.read_registration = lambda _path: registration
    V4.validate_registration = validate_registration
    V4.V3.V2.offline_probe = structural_probe
    V4.RESULT_SCHEMA = RESULT_SCHEMA
    return V4.run_preparation(args)


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
