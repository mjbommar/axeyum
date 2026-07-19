#!/usr/bin/env python3
"""Materialize the exact preregistered real-query proof holdout corpus."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
from pathlib import Path
from typing import Any


FULL_MANIFEST_SHA256 = (
    "c3cad70caff90d7f1528196e306cbb45808c14f839f07e742aac6ad2f0ade75c"
)
SELECTED_MANIFEST_SHA256 = (
    "67c7f14f5f2f8db1eaa1bb17649cf3623e268e3f7ea678cbe53326bfa8cd899b"
)
EXPECTED_SELECTED = 1024
QUERY_PATH = re.compile(r"queries/[0-9a-f]{64}\.smt2\Z")


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _validated_entries(value: Any, label: str) -> list[dict[str, Any]]:
    if not isinstance(value, dict):
        raise ValueError(f"{label} must be an object")
    if value.get("version") != 1:
        raise ValueError(f"{label} version must be 1")
    if value.get("logic") != "QF_BV":
        raise ValueError(f"{label} logic must be QF_BV")
    files = value.get("files")
    if not isinstance(files, list):
        raise ValueError(f"{label} files must be an array")
    entries: list[dict[str, Any]] = []
    hashes: set[str] = set()
    paths: set[str] = set()
    for index, raw in enumerate(files):
        if not isinstance(raw, dict):
            raise ValueError(f"{label} files[{index}] must be an object")
        path = raw.get("path")
        content_hash = raw.get("content_hash")
        expected = raw.get("expected")
        family = raw.get("family")
        tiers = raw.get("tiers")
        if not isinstance(path, str) or QUERY_PATH.fullmatch(path) is None:
            raise ValueError(f"{label} files[{index}] has an invalid path")
        if (
            not isinstance(content_hash, str)
            or not content_hash.startswith("sha256:")
            or len(content_hash) != 71
            or re.fullmatch(r"[0-9a-f]{64}", content_hash[7:]) is None
        ):
            raise ValueError(f"{label} files[{index}] has an invalid content hash")
        if expected not in ("sat", "unsat"):
            raise ValueError(f"{label} files[{index}] has an invalid expected verdict")
        if not isinstance(family, str) or not family:
            raise ValueError(f"{label} files[{index}] has an invalid family")
        if not isinstance(tiers, list) or not tiers:
            raise ValueError(f"{label} files[{index}] has no tier")
        if path in paths:
            raise ValueError(f"{label} repeats a duplicate path")
        if content_hash in hashes:
            raise ValueError(f"{label} repeats a duplicate content hash")
        paths.add(path)
        hashes.add(content_hash)
        entries.append(raw)
    return entries


def materialize(
    source_root: Path,
    full_manifest_path: Path,
    selected_manifest_path: Path,
    destination: Path,
    *,
    expected_full_sha256: str,
    expected_selected_sha256: str,
) -> dict[str, Any]:
    """Copy only exact selected members after completing all source checks."""

    if destination.exists():
        raise ValueError(f"refusing to overwrite existing destination {destination}")
    full_raw = full_manifest_path.read_bytes()
    selected_raw = selected_manifest_path.read_bytes()
    full_sha = sha256(full_raw)
    selected_sha = sha256(selected_raw)
    if full_sha != expected_full_sha256:
        raise ValueError("full manifest SHA-256 differs from the preregistration")
    if selected_sha != expected_selected_sha256:
        raise ValueError("selected manifest SHA-256 differs from the preregistration")

    full_entries = _validated_entries(json.loads(full_raw), "full manifest")
    selected_entries = _validated_entries(
        json.loads(selected_raw), "selected manifest"
    )
    full_by_hash = {row["content_hash"]: row for row in full_entries}
    identity = ("path", "content_hash", "expected", "family")
    preflight: list[tuple[dict[str, Any], Path, bytes]] = []
    copied_bytes = 0
    for row in selected_entries:
        source_member = full_by_hash.get(row["content_hash"])
        if source_member is None or any(
            source_member[key] != row[key] for key in identity
        ):
            raise ValueError(
                "selected entry is not an exact full-manifest member: "
                f"{row['content_hash']}"
            )
        source_path = source_root / row["path"]
        if not source_path.is_file():
            raise ValueError(f"selected source file is missing: {row['path']}")
        raw = source_path.read_bytes()
        if sha256(raw) != row["content_hash"][7:]:
            raise ValueError(f"selected source content hash differs: {row['path']}")
        preflight.append((row, source_path, raw))
        copied_bytes += len(raw)

    destination.mkdir(parents=True)
    for row, source_path, raw in preflight:
        destination_path = destination / row["path"]
        destination_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source_path, destination_path)
        if destination_path.read_bytes() != raw:
            raise ValueError(f"copied query bytes differ: {row['path']}")
    (destination / "manifest-v1.json").write_bytes(selected_raw)

    expected_paths = sorted(row["path"] for row in selected_entries)
    discovered_paths = sorted(
        path.relative_to(destination).as_posix()
        for path in destination.rglob("*.smt2")
    )
    if discovered_paths != expected_paths:
        raise ValueError("materialized corpus membership differs from selection")
    query_set_raw = "".join(
        f"{row['path']}\0{row['content_hash']}\n"
        for row in sorted(selected_entries, key=lambda item: item["path"])
    ).encode()
    return {
        "schema": "axeyum.qfbv-proof-holdout-materialization.v1",
        "source_root": str(source_root),
        "full_manifest": str(full_manifest_path),
        "full_manifest_sha256": full_sha,
        "selected_manifest": str(selected_manifest_path),
        "selected_manifest_sha256": selected_sha,
        "destination": str(destination),
        "destination_manifest": str(destination / "manifest-v1.json"),
        "selected_entries": len(selected_entries),
        "copied_bytes": copied_bytes,
        "query_set_sha256": sha256(query_set_raw),
        "exact_membership": True,
        "all_source_hashes_verified": True,
        "all_destination_bytes_verified": True,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--full-manifest", type=Path, required=True)
    parser.add_argument("--selected-manifest", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    report = materialize(
        args.source_root,
        args.full_manifest,
        args.selected_manifest,
        args.out,
        expected_full_sha256=FULL_MANIFEST_SHA256,
        expected_selected_sha256=SELECTED_MANIFEST_SHA256,
    )
    if report["selected_entries"] != EXPECTED_SELECTED:
        raise ValueError("selected cardinality differs from the preregistration")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
