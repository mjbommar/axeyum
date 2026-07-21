#!/usr/bin/env python3
"""Prepare ADR-0331's hard-link-aware, inventoried Tock Cargo cache."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import stat
import sys
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
V3 = load_support(
    "tock_cache_v3_support", REPO / "scripts/prepare-tock-log2-cache-v3.py"
)
SUPPORT = V3.SUPPORT
V3_VALIDATE_REGISTRATION = V3.validate_registration
DEFAULT_REGISTRATION = (
    REPO
    / "bench-results/verify-tock-log2-20260721/cache-v4-preparation-registration.json"
)
BASE_REGISTRATION = (
    REPO
    / "bench-results/verify-tock-log2-20260721/cache-v3-preparation-registration.json"
)
BASE_REGISTRATION_IDENTITY = {
    "path": "bench-results/verify-tock-log2-20260721/cache-v3-preparation-registration.json",
    "sha256": "ff19ef30f865d1ee34fb252d665a79a74c5e697cd560cd23552d571002fa59fb",
}
DEFAULT_TOCK_REPO = REPO / "references/tock"
DEFAULT_OUTPUT = REPO / "target/tock-log2-20260721/cache-v4"
REGISTRATION_SCHEMA = "axeyum.tock-log2-cache-v4-preparation-registration.v1"
RESULT_SCHEMA = "axeyum.tock-log2-cache-v4-preparation-result.v1"
INVENTORY_SCHEMA = "axeyum.cargo-cache-hardlink-inventory.v1"


CaptureError = SUPPORT.CaptureError
fail = SUPPORT.fail
require = SUPPORT.require
require_string = SUPPORT.require_string


def read_registration(path: Path) -> dict[str, Any]:
    overlay = SUPPORT.read_json(path)
    require(
        set(overlay)
        == {"schema", "base_registration", "inventory_schema", "producer_files"},
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
        overlay.get("inventory_schema") == INVENTORY_SCHEMA,
        "registration",
        "inventory_schema",
        str(overlay.get("inventory_schema")),
    )
    SUPPORT.validate_file(
        BASE_REGISTRATION,
        BASE_REGISTRATION_IDENTITY["sha256"],
        "registration",
        "base_registration",
    )
    base = V3.read_registration(BASE_REGISTRATION)
    V3_VALIDATE_REGISTRATION(base)
    producers = overlay.get("producer_files")
    require(isinstance(producers, list) and producers, "registration", "shape", "producer_files")
    registration = json.loads(json.dumps(base))
    registration["schema"] = REGISTRATION_SCHEMA
    registration["base_registration"] = BASE_REGISTRATION_IDENTITY
    registration["inventory_schema"] = INVENTORY_SCHEMA
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
        registration.get("inventory_schema") == INVENTORY_SCHEMA,
        "registration",
        "inventory_schema",
        str(registration.get("inventory_schema")),
    )
    inherited = json.loads(json.dumps(registration))
    inherited["schema"] = V3.REGISTRATION_SCHEMA
    inherited["base_registration"] = V3.BASE_REGISTRATION_IDENTITY
    V3_VALIDATE_REGISTRATION(inherited)


def inventory_cache(root: Path) -> dict[str, Any]:
    require(root.is_dir() and not root.is_symlink(), "inventory", "root", str(root))
    root_resolved = root.resolve()
    paths = sorted(root.rglob("*"), key=lambda value: value.relative_to(root).as_posix())
    metadata = {path: path.lstat() for path in paths}
    groups: dict[tuple[int, int], list[Path]] = {}
    for path in paths:
        info = metadata[path]
        if stat.S_ISREG(info.st_mode):
            groups.setdefault((info.st_dev, info.st_ino), []).append(path)

    file_rows: dict[Path, dict[str, Any]] = {}
    distinct_bytes = 0
    path_bytes = 0
    hardlinks = 0
    hardlink_groups = 0
    for members in groups.values():
        members.sort(key=lambda value: value.relative_to(root).as_posix())
        owner = members[0]
        owner_info = metadata[owner]
        mode = stat.S_IMODE(owner_info.st_mode)
        size = owner_info.st_size
        digest = SUPPORT.sha256_file(owner)
        links = len(members)
        if links > 1:
            hardlink_groups += 1
        for member in members:
            info = metadata[member]
            relative = member.relative_to(root).as_posix()
            require(
                stat.S_IMODE(info.st_mode) == mode
                and info.st_size == size
                and info.st_nlink == links,
                "inventory",
                "hardlink_metadata",
                relative,
            )
            require(
                not relative.endswith((".part", ".tmp")),
                "inventory",
                "temporary_path",
                relative,
            )
            common = {
                "links": links,
                "mode": mode,
                "path": relative,
                "sha256": digest,
                "size": size,
            }
            if member == owner:
                file_rows[member] = {"kind": "file", **common}
            else:
                file_rows[member] = {
                    "kind": "hardlink",
                    **common,
                    "target": owner.relative_to(root).as_posix(),
                }
                hardlinks += 1
            path_bytes += size
        distinct_bytes += size

    rows: list[dict[str, Any]] = []
    counts = {"directories": 0, "files": 0, "symlinks": 0}
    for path in paths:
        relative = path.relative_to(root).as_posix()
        info = metadata[path]
        mode = stat.S_IMODE(info.st_mode)
        if stat.S_ISDIR(info.st_mode):
            rows.append({"kind": "directory", "mode": mode, "path": relative})
            counts["directories"] += 1
        elif stat.S_ISREG(info.st_mode):
            row = file_rows[path]
            rows.append(row)
            if row["kind"] == "file":
                counts["files"] += 1
        elif stat.S_ISLNK(info.st_mode):
            target = os.readlink(path)
            require(
                not Path(target).is_absolute(),
                "inventory",
                "absolute_symlink",
                f"{relative}={target}",
            )
            resolved = path.resolve(strict=False)
            require(
                resolved.is_relative_to(root_resolved),
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
        "schema": INVENTORY_SCHEMA,
        "sha256": SUPPORT.sha256_bytes(canonical),
        "rows": len(rows),
        **counts,
        "hardlinks": hardlinks,
        "hardlink_groups": hardlink_groups,
        "bytes": distinct_bytes,
        "path_bytes": path_bytes,
        "registry_packages": registry_packages,
        "git_checkouts": git_checkouts,
    }


def run_preparation(args: argparse.Namespace) -> dict[str, Any]:
    registration = read_registration(args.registration.resolve())
    validate_registration(registration)
    V3.read_registration = lambda _path: registration
    V3.validate_registration = validate_registration
    V3.V2.inventory_cache = inventory_cache
    V3.RESULT_SCHEMA = RESULT_SCHEMA
    return V3.run_preparation(args)


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
