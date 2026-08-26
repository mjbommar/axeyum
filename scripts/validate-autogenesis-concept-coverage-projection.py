#!/usr/bin/env python3
"""Validate the local, held-out-safe concept coverage projection."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
AUTO = ROOT / "artifacts/autogenesis"
P = AUTO / "concept-coverage-projection-v1.json"
SOURCES = {
    "catalog_sha256": AUTO / "mathlib-nat-int-fact-catalog-v1.json",
    "crosswalk_sha256": AUTO / "family-concept-crosswalk-v1.json",
    "nursery_sha256": AUTO / "nursery-v1.json",
    "knowledge_overlay_sha256": AUTO / "knowledge-overlay-v1.json",
}


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(document: dict) -> list[str]:
    errors: list[str] = []
    if document.get("kind") != "axeyum-autogenesis-concept-coverage-projection":
        return ["invalid projection kind"]
    derivation = document.get("derivation", {})
    if (
        not isinstance(derivation, dict)
        or derivation.get("evaluation_partitions") != ["development", "train"]
        or "never held-out" not in derivation.get("trust_boundary", "")
    ):
        errors.append("missing held-out isolation boundary")
    for key, path in SOURCES.items():
        if derivation.get(key) != sha(path):
            errors.append(f"stale {key}")

    nursery = json.loads(SOURCES["nursery_sha256"].read_text())
    held = {row["fact_id"] for row in nursery["entries"] if row["partition"] == "held-out"}
    overlay = json.loads(SOURCES["knowledge_overlay_sha256"].read_text())
    expected_facts: dict[str, set[str]] = {}
    expected_anchors: dict[str, set[str]] = {}
    for link in overlay["links"]:
        if link["relation"] != "formalizes" or link["status"] != "active":
            continue
        concept = link["target"]["id"]
        source = link["source"]
        if source["kind"] == "fact" and source["id"] not in held:
            expected_facts.setdefault(concept, set()).add(source["id"])
        elif source["kind"] == "kernel-declaration":
            expected_anchors.setdefault(concept, set()).add(source["id"])

    rows = document.get("concepts", [])
    seen: set[str] = set()
    all_topic: set[str] = set()
    all_formalized: set[str] = set()
    all_anchors: set[str] = set()
    for row in rows:
        ident = row.get("concept_id")
        if not isinstance(ident, str) or ident in seen:
            errors.append("concept ids must be unique strings")
            continue
        seen.add(ident)
        for field, count_field in (
            ("family_topic_fact_ids", "family_topic_fact_count"),
            ("qualified_formalization_fact_ids", "qualified_formalization_fact_count"),
            ("kernel_semantic_anchor_ids", "kernel_semantic_anchor_count"),
        ):
            values = row.get(field)
            if not isinstance(values, list) or values != sorted(set(values)):
                errors.append(f"{ident}: {field} must be sorted and unique")
                continue
            if row.get(count_field) != len(values):
                errors.append(f"{ident}: {count_field} disagrees")
        fact_ids = set(row.get("qualified_formalization_fact_ids", []))
        anchors = set(row.get("kernel_semantic_anchor_ids", []))
        if fact_ids != expected_facts.get(ident, set()):
            errors.append(f"{ident}: qualified formalizations disagree with overlay")
        if anchors != expected_anchors.get(ident, set()):
            errors.append(f"{ident}: kernel anchors disagree with overlay")
        all_topic.update(row.get("family_topic_fact_ids", []))
        all_formalized.update(fact_ids)
        all_anchors.update(anchors)
    if held.intersection(all_topic | all_formalized):
        errors.append("projection discloses a held-out fact id")
    if (set(expected_facts) | set(expected_anchors)) - seen:
        errors.append("projection omits a locally reviewed semantic concept")

    census = document.get("census", {})
    expected_census = {
        "concepts": len(rows),
        "with_family_topic": sum(bool(row.get("family_topic_fact_ids")) for row in rows),
        "with_qualified_formalizations": sum(
            bool(row.get("qualified_formalization_fact_ids")) for row in rows
        ),
        "with_kernel_semantic_anchors": sum(
            bool(row.get("kernel_semantic_anchor_ids")) for row in rows
        ),
        "family_topic_facts": len(all_topic),
        "qualified_formalization_facts": len(all_formalized),
        "kernel_semantic_anchors": len(all_anchors),
    }
    for key, expected in expected_census.items():
        if census.get(key) != expected:
            errors.append(f"coverage census {key} disagrees")
    if census.get("excluded_held_out_formalizations") != 0:
        errors.append("held-out formalization edges exist and require review")
    return errors


def main() -> int:
    document = json.loads(P.read_text())
    errors = validate(document)
    for error in errors:
        print("AUTOGENESIS_CONCEPT_COVERAGE_ERROR|" + error, file=sys.stderr)
    if errors:
        return 1
    census = document["census"]
    print(
        "AUTOGENESIS_CONCEPT_COVERAGE_OK|"
        f"concepts={census['concepts']}|topic_facts={census['family_topic_facts']}|"
        f"formalized_facts={census['qualified_formalization_facts']}|"
        f"kernel_anchors={census['kernel_semantic_anchors']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
