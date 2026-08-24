#!/usr/bin/env python3
"""Derive a review queue for kernel theorems not yet semantically anchored.

This is deliberately a queue for human review, not a concept classifier or a
scheduler.  Its ordering is a deterministic graph observation only: direct
reverse theorem-reference count, then direct dependency count, then name.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from collections import Counter
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
KERNEL = ROOT / "artifacts/autogenesis/kernel-dependency-projection-v1.json"
OVERLAY = ROOT / "artifacts/autogenesis/knowledge-overlay-v1.json"
OUTPUT = ROOT / "artifacts/autogenesis/kernel-semantic-review-queue-v1.json"


def digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build() -> dict[str, Any]:
    kernel = json.loads(KERNEL.read_text())
    overlay = json.loads(OVERLAY.read_text())
    declarations = kernel["declarations"]
    anchored = {
        link["source"]["id"]
        for link in overlay["links"]
        if link["relation"] == "formalizes"
        and link["status"] == "active"
        and link["source"]["namespace"] == "axeyum-kernel"
        and link["source"]["kind"] == "kernel-declaration"
    }
    reverse = Counter(edge["target"] for edge in kernel["direct_theorem_dependency_edges"])
    eligible = [
        declaration
        for declaration in declarations
        if declaration["declaration_kind"] == "theorem"
        and declaration["axiom_footprint_size"] == 0
    ]
    queue = [
        {
            "kernel_declaration_id": declaration["id"],
            "visible_in": declaration["visible_in"],
            "direct_theorem_dependency_count": len(
                declaration["direct_theorem_dependencies"]
            ),
            "direct_reverse_theorem_reference_count": reverse[declaration["id"]],
            "review_status": "unreviewed",
            "selection_basis": "mechanical graph ordering only; no topic, proof technique, capability, or concept claim",
        }
        for declaration in eligible
        if declaration["id"] not in anchored
    ]
    queue.sort(
        key=lambda row: (
            -row["direct_reverse_theorem_reference_count"],
            -row["direct_theorem_dependency_count"],
            row["kernel_declaration_id"],
        )
    )
    return {
        "schema_version": 1,
        "kind": "axeyum-kernel-semantic-review-queue",
        "derivation": {
            "kernel_projection_sha256": digest(KERNEL),
            "knowledge_overlay_sha256": digest(OVERLAY),
            "candidate_rule": "theorem with empty recorded axiom footprint and no active kernel-source formalizes link",
            "ordering": "descending direct reverse theorem-reference count, descending direct theorem-dependency count, ascending declaration id",
            "trust_boundary": "review planning only; never concept classification, producer dispatch, proof, admission, or trusted-kernel authority",
        },
        "census": {
            "kernel_theorems": sum(
                declaration["declaration_kind"] == "theorem" for declaration in declarations
            ),
            "empty_footprint_theorems": len(eligible),
            "reviewed_kernel_semantic_anchors": len(anchored),
            "unreviewed_queue_entries": len(queue),
        },
        "reviewed_kernel_semantic_anchor_ids": sorted(anchored),
        "unreviewed_entries": queue,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text() != rendered:
            print("AUTOGENESIS_KERNEL_SEMANTIC_QUEUE_ERROR|queue is stale", file=sys.stderr)
            return 1
    else:
        OUTPUT.write_text(rendered)
    census = json.loads(rendered)["census"]
    print(
        "AUTOGENESIS_KERNEL_SEMANTIC_QUEUE|"
        f"theorems={census['kernel_theorems']}|"
        f"anchored={census['reviewed_kernel_semantic_anchors']}|"
        f"unreviewed={census['unreviewed_queue_entries']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
