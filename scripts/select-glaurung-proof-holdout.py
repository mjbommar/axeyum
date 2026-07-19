#!/usr/bin/env python3
"""Select the preregistered corrected-wide-v3 real-query proof holdout."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path
from typing import Any


FULL_MANIFEST_SHA256 = (
    "c3cad70caff90d7f1528196e306cbb45808c14f839f07e742aac6ad2f0ade75c"
)
REPRESENTATIVE_MANIFEST_SHA256 = (
    "7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064"
)
SOURCE_MANIFEST_NAME = "glaurung-qfbv-2026-07-16-corrected-wide-v3"
OUTPUT_MANIFEST_NAME = f"{SOURCE_MANIFEST_NAME}-proof-holdout-v1"
OUTPUT_TIER = "proof-holdout-v1"
QUOTAS = {
    ("arithmetic", "sat"): 170,
    ("arithmetic", "unsat"): 170,
    ("comparison", "sat"): 6,
    ("register-slice", "sat"): 170,
    ("register-slice", "unsat"): 170,
    ("slice-partial", "sat"): 169,
    ("slice-partial", "unsat"): 169,
}
EXPECTED_SELECTED = 1024


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
        if not isinstance(path, str) or not path.startswith("queries/"):
            raise ValueError(f"{label} files[{index}] has an invalid path")
        if (
            not isinstance(content_hash, str)
            or not content_hash.startswith("sha256:")
            or len(content_hash) != 71
        ):
            raise ValueError(f"{label} files[{index}] has an invalid content hash")
        if expected not in ("sat", "unsat"):
            raise ValueError(f"{label} files[{index}] has an invalid expected verdict")
        if not isinstance(family, str) or not family:
            raise ValueError(f"{label} files[{index}] has an invalid family")
        if not isinstance(tiers, list) or not tiers:
            raise ValueError(f"{label} files[{index}] has no tier")
        if content_hash in hashes:
            raise ValueError(f"{label} repeats a duplicate content hash")
        if path in paths:
            raise ValueError(f"{label} repeats a duplicate path")
        hashes.add(content_hash)
        paths.add(path)
        entries.append(raw)
    return entries


def select_manifest(
    full_manifest: dict[str, Any],
    representative_manifest: dict[str, Any],
    *,
    quotas: dict[tuple[str, str], int],
    output_name: str,
    tier: str,
) -> dict[str, Any]:
    """Select the lowest content hashes per stratum after exact exclusion."""

    full_entries = _validated_entries(full_manifest, "full manifest")
    representative_entries = _validated_entries(
        representative_manifest, "representative manifest"
    )
    full_by_hash = {row["content_hash"]: row for row in full_entries}
    excluded: set[str] = set()
    for row in representative_entries:
        candidate = full_by_hash.get(row["content_hash"])
        identity = ("path", "content_hash", "expected", "family")
        if candidate is None or any(candidate[key] != row[key] for key in identity):
            raise ValueError(
                "representative entry is not an exact full-manifest member: "
                f"{row['content_hash']}"
            )
        excluded.add(row["content_hash"])

    strata: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for row in full_entries:
        if row["content_hash"] not in excluded:
            strata[(row["family"], row["expected"])].append(row)
    for rows in strata.values():
        rows.sort(key=lambda row: row["content_hash"])

    selected: list[dict[str, Any]] = []
    for stratum, quota in sorted(quotas.items()):
        if type(quota) is not int or quota < 0:
            raise ValueError(f"invalid quota for {stratum}: {quota!r}")
        available = strata.get(stratum, [])
        if len(available) < quota:
            raise ValueError(
                f"stratum {stratum} has {len(available)} rows below quota {quota}"
            )
        for row in available[:quota]:
            selected.append(
                {
                    "path": row["path"],
                    "content_hash": row["content_hash"],
                    "expected": row["expected"],
                    "family": row["family"],
                    "tiers": [tier],
                }
            )
    selected.sort(key=lambda row: row["content_hash"])
    if len({row["content_hash"] for row in selected}) != len(selected):
        raise ValueError("selection contains duplicate content hashes")
    return {
        "version": 1,
        "name": output_name,
        "logic": "QF_BV",
        "source": (
            "Content-hash-first stratified holdout from corrected-wide-v3/full; "
            "excludes every corrected-wide-v3 representative hash before fixed "
            "family/verdict quotas; selection is independent of proof completion "
            "and timing"
        ),
        "files": selected,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full-manifest", type=Path, required=True)
    parser.add_argument("--representative-manifest", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        parser.error(f"refusing to overwrite {args.out}")

    full_raw = args.full_manifest.read_bytes()
    representative_raw = args.representative_manifest.read_bytes()
    if sha256(full_raw) != FULL_MANIFEST_SHA256:
        raise ValueError("full manifest SHA-256 differs from the preregistration")
    if sha256(representative_raw) != REPRESENTATIVE_MANIFEST_SHA256:
        raise ValueError(
            "representative manifest SHA-256 differs from the preregistration"
        )
    full_manifest = json.loads(full_raw)
    representative_manifest = json.loads(representative_raw)
    if full_manifest.get("name") != SOURCE_MANIFEST_NAME:
        raise ValueError("full manifest name differs from the preregistration")
    if representative_manifest.get("name") != SOURCE_MANIFEST_NAME:
        raise ValueError("representative manifest name differs from the preregistration")

    selected = select_manifest(
        full_manifest,
        representative_manifest,
        quotas=QUOTAS,
        output_name=OUTPUT_MANIFEST_NAME,
        tier=OUTPUT_TIER,
    )
    if len(selected["files"]) != EXPECTED_SELECTED:
        raise ValueError("selected manifest cardinality differs from preregistration")
    args.out.parent.mkdir(parents=True, exist_ok=True)
    rendered = json.dumps(selected, indent=2) + "\n"
    args.out.write_text(rendered, encoding="utf-8")
    summary = {
        "output": str(args.out),
        "output_sha256": sha256(rendered.encode()),
        "selected": len(selected["files"]),
        "excluded_representative": len(representative_manifest["files"]),
        "quotas": {
            f"{family}/{expected}": quota
            for (family, expected), quota in sorted(QUOTAS.items())
        },
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
