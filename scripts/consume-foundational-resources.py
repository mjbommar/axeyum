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
ROW_LABELS = {
    ("sat", "checked"): "checked witness",
    ("sat", "replay-only"): "finite witness replay",
    ("unsat", "checked"): "checked refutation",
    ("unsat", "replay-only"): "finite rejection replay",
    ("not-run", "lean-horizon"): "theorem horizon",
}


class ConsumerError(Exception):
    pass


def fail(message: str) -> None:
    raise ConsumerError(message)


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def count_text(counter: Counter[str]) -> str:
    return ",".join(f"{key}:{counter[key]}" for key in sorted(counter))


def label_key(label: str) -> str:
    return label.replace(" ", "_").replace("-", "_")


def row_display_label(result: str, proof_status: str) -> str:
    label = ROW_LABELS.get((result, proof_status))
    if label is None:
        fail(f"unrecognized result/proof-status label pair: {result}/{proof_status}")
    return label


def pack_display_labels(checks: list[dict[str, Any]]) -> list[str]:
    proof_statuses = {
        check.get("proof_status", "")
        for check in checks
        if check.get("proof_status")
    }
    labels = []
    if "checked" in proof_statuses:
        labels.append("checked evidence pack")
    elif "replay-only" in proof_statuses:
        labels.append("finite replay pack")
    if "lean-horizon" in proof_statuses:
        labels.append("theorem boundary included")
    if len(proof_statuses) > 1:
        labels.append("mixed trust story")
    if not labels:
        fail("pack has no display label")
    return labels


def main() -> int:
    atlas = load_json(ATLAS)
    if atlas.get("schema_version") != 1:
        fail("foundational atlas schema_version must be 1")
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
    result_counts: Counter[str] = Counter()
    row_label_counts: Counter[str] = Counter()
    pack_label_counts: Counter[str] = Counter()
    non_template_pack_ids: set[str] = set()
    checked_pack_ids: set[str] = set()
    for metadata_path in sorted(EXAMPLE_ROOT.glob("*/metadata.json")):
        metadata = load_json(metadata_path)
        if metadata.get("schema_version") != 1:
            fail(f"{metadata_path} schema_version must be 1")
        pack_id = metadata.get("id")
        if pack_id != metadata_path.parent.name:
            fail(f"{metadata_path} id does not match directory name")
        if metadata.get("claim_status") == "template":
            continue

        expected_path = metadata_path.parent / "expected.json"
        expected = load_json(expected_path)
        if expected.get("schema_version") != 1:
            fail(f"{expected_path} schema_version must be 1")
        if expected.get("pack_id") != pack_id:
            fail(f"{expected_path} pack_id does not match metadata id")
        non_template_pack_ids.add(pack_id)

        pack_has_checked = False
        checks = expected.get("checks", [])
        for check in checks:
            result = check.get("expected_result")
            if not result:
                fail(f"{expected_path} has a check with no expected_result")
            result_counts[result] += 1
            status = check.get("proof_status")
            if not status:
                fail(f"{expected_path} has a check with no proof_status")
            proof_counts[status] += 1
            row_label_counts[label_key(row_display_label(result, status))] += 1
            pack_has_checked = pack_has_checked or status == "checked"
        if pack_has_checked:
            checked_pack_ids.add(pack_id)
        for label in pack_display_labels(checks):
            pack_label_counts[label_key(label)] += 1

    missing_from_atlas = sorted(non_template_pack_ids - atlas_pack_ids)
    if missing_from_atlas:
        fail("non-template packs missing from atlas rows: " + ", ".join(missing_from_atlas))

    print("foundational resource consumer smoke")
    print(f"concept_rows={len(rows)}")
    print(f"curriculum_rows={row_counts['curriculum-node']}")
    print(f"field_rows={row_counts['field']}")
    print(f"non_template_packs={len(non_template_pack_ids)}")
    print(f"packs_with_checked_evidence={len(checked_pack_ids)}")
    print("schema_versions=atlas:1,metadata:1,expected:1")
    print("expected_result_counts=" + count_text(result_counts))
    print("proof_status_counts=" + count_text(proof_counts))
    print("row_label_counts=" + count_text(row_label_counts))
    print("pack_label_counts=" + count_text(pack_label_counts))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
