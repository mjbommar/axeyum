#!/usr/bin/env python3
"""Join reviewed family topics to local qualified semantic coverage."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from collections import defaultdict

ROOT = pathlib.Path(__file__).resolve().parents[1]
AUTO = ROOT / "artifacts/autogenesis"
OUT = AUTO / "concept-coverage-projection-v1.json"
CATALOG = AUTO / "mathlib-nat-int-fact-catalog-v1.json"
CROSSWALK = AUTO / "family-concept-crosswalk-v1.json"
NURSERY = AUTO / "nursery-v1.json"
OVERLAY = AUTO / "knowledge-overlay-v1.json"


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def endpoint(link: dict, side: str) -> tuple[str, str, str]:
    value = link[side]
    return value["namespace"], value["kind"], value["id"]


def build() -> dict:
    catalog = json.loads(CATALOG.read_text())
    crosswalk = json.loads(CROSSWALK.read_text())
    nursery = json.loads(NURSERY.read_text())
    overlay = json.loads(OVERLAY.read_text())
    partition = {row["fact_id"]: row["partition"] for row in nursery["entries"]}
    visible = {"train", "development"}

    families: dict[str, list[str]] = defaultdict(list)
    for row in catalog["facts"]:
        families[row["family"]].append(row["fact_id"])
    topic: dict[str, list[str]] = defaultdict(list)
    for row in crosswalk["mappings"]:
        topic[row["concept_id"]].extend(
            fact_id for fact_id in families[row["family"]] if partition.get(fact_id) in visible
        )

    formalized: dict[str, list[str]] = defaultdict(list)
    anchors: dict[str, list[str]] = defaultdict(list)
    excluded_held_out_formalizations = 0
    for link in overlay["links"]:
        if link["relation"] != "formalizes" or link["status"] != "active":
            continue
        target = endpoint(link, "target")
        if target[:2] != ("axeyum-knowledge", "concept"):
            continue
        source = endpoint(link, "source")
        if source[1] == "fact":
            if partition.get(source[2]) in visible:
                formalized[target[2]].append(source[2])
            elif partition.get(source[2]) == "held-out":
                excluded_held_out_formalizations += 1
        elif source[1] == "kernel-declaration":
            anchors[target[2]].append(source[2])

    rows = []
    for concept in sorted(set(topic) | set(formalized) | set(anchors)):
        topic_ids = sorted(set(topic[concept]))
        fact_ids = sorted(set(formalized[concept]))
        anchor_ids = sorted(set(anchors[concept]))
        dimensions = [
            name
            for name, present in (
                ("family-topic", topic_ids),
                ("qualified-facts", fact_ids),
                ("kernel-anchors", anchor_ids),
            )
            if present
        ]
        rows.append(
            {
                "concept_id": concept,
                "family_topic_fact_ids": topic_ids,
                "family_topic_fact_count": len(topic_ids),
                "qualified_formalization_fact_ids": fact_ids,
                "qualified_formalization_fact_count": len(fact_ids),
                "kernel_semantic_anchor_ids": anchor_ids,
                "kernel_semantic_anchor_count": len(anchor_ids),
                "coverage_state": "+".join(dimensions),
                "trust": "family topics are reviewed guidance; semantic edges are human-reviewed partial mappings; none grants proof, operation, or admission authority",
            }
        )

    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-concept-coverage-projection",
        "derivation": {
            "catalog_sha256": sha(CATALOG),
            "crosswalk_sha256": sha(CROSSWALK),
            "nursery_sha256": sha(NURSERY),
            "knowledge_overlay_sha256": sha(OVERLAY),
            "evaluation_partitions": ["development", "train"],
            "trust_boundary": "train/development fact coverage plus local reviewed kernel anchors only; never held-out disclosure, proof, operation, or admission authority",
        },
        "census": {
            "concepts": len(rows),
            "with_family_topic": sum(bool(row["family_topic_fact_ids"]) for row in rows),
            "with_qualified_formalizations": sum(
                bool(row["qualified_formalization_fact_ids"]) for row in rows
            ),
            "with_kernel_semantic_anchors": sum(
                bool(row["kernel_semantic_anchor_ids"]) for row in rows
            ),
            "family_topic_facts": len(
                {fact for row in rows for fact in row["family_topic_fact_ids"]}
            ),
            "qualified_formalization_facts": len(
                {fact for row in rows for fact in row["qualified_formalization_fact_ids"]}
            ),
            "kernel_semantic_anchors": len(
                {anchor for row in rows for anchor in row["kernel_semantic_anchor_ids"]}
            ),
            "excluded_held_out_family_topic_facts": sum(
                1 for row in catalog["facts"] if partition.get(row["fact_id"]) == "held-out"
            ),
            "excluded_held_out_formalizations": excluded_held_out_formalizations,
        },
        "concepts": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    document = build()
    rendered = json.dumps(document, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not OUT.is_file() or OUT.read_text() != rendered:
            print("AUTOGENESIS_CONCEPT_COVERAGE_ERROR|projection is stale", file=sys.stderr)
            return 1
    else:
        OUT.write_text(rendered)
    census = document["census"]
    print(
        "AUTOGENESIS_CONCEPT_COVERAGE|"
        f"concepts={census['concepts']}|topic_facts={census['family_topic_facts']}|"
        f"formalized_facts={census['qualified_formalization_facts']}|"
        f"kernel_anchors={census['kernel_semantic_anchors']}|"
        f"held_out_formalizations={census['excluded_held_out_formalizations']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
