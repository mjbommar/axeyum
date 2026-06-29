#!/usr/bin/env python3
"""Smoke-test the public foundational-resource data contract.

This script intentionally does not import the validators or generators. It is a
tiny downstream-consumer stand-in: read the committed atlas plus example-pack
metadata/expected JSON files, cross-check basic references, and print a stable
summary. If this script breaks, the resource data is no longer easy to consume
from outside the implementation scripts.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
ATLAS = ROOT / "artifacts" / "ontology" / "foundational-concepts.json"
EXAMPLE_ROOT = ROOT / "artifacts" / "examples" / "math"


class ConsumerError(Exception):
    pass


def fail(message: str) -> None:
    raise ConsumerError(message)


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def main() -> int:
    atlas = load_json(ATLAS)
    rows = atlas.get("rows", [])
    if not rows:
        fail("foundational atlas has no rows")

    row_counts = Counter(row.get("kind") for row in rows)
    atlas_pack_ids = {
        pack["id"]
        for row in rows
        for pack in row.get("example_packs", [])
        if pack.get("status") == "validated"
    }

    proof_counts: Counter[str] = Counter()
    non_template_pack_ids: set[str] = set()
    checked_pack_ids: set[str] = set()
    for metadata_path in sorted(EXAMPLE_ROOT.glob("*/metadata.json")):
        metadata = load_json(metadata_path)
        pack_id = metadata.get("id")
        if pack_id != metadata_path.parent.name:
            fail(f"{metadata_path} id does not match directory name")
        if metadata.get("claim_status") == "template":
            continue

        expected_path = metadata_path.parent / "expected.json"
        expected = load_json(expected_path)
        if expected.get("pack_id") != pack_id:
            fail(f"{expected_path} pack_id does not match metadata id")
        non_template_pack_ids.add(pack_id)

        pack_has_checked = False
        for check in expected.get("checks", []):
            status = check.get("proof_status")
            if not status:
                fail(f"{expected_path} has a check with no proof_status")
            proof_counts[status] += 1
            pack_has_checked = pack_has_checked or status == "checked"
        if pack_has_checked:
            checked_pack_ids.add(pack_id)

    missing_from_atlas = sorted(non_template_pack_ids - atlas_pack_ids)
    if missing_from_atlas:
        fail("non-template packs missing from atlas rows: " + ", ".join(missing_from_atlas))

    print("foundational resource consumer smoke")
    print(f"concept_rows={len(rows)}")
    print(f"curriculum_rows={row_counts['curriculum-node']}")
    print(f"field_rows={row_counts['field']}")
    print(f"non_template_packs={len(non_template_pack_ids)}")
    print(f"packs_with_checked_evidence={len(checked_pack_ids)}")
    print(
        "proof_status_counts="
        + ",".join(f"{status}:{proof_counts[status]}" for status in sorted(proof_counts))
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
