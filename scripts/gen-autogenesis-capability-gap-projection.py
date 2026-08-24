#!/usr/bin/env python3
"""Derive the non-authoritative gap between the ready fact frontier and producers.

This is deliberately a queue diagnostic, not an operation registry and not
admission authority.  It takes the content-addressed fact-frontier selection
as its sole source, then groups dependency-ready facts by their typed formal
surface and records why each group cannot currently be dispatched.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import pathlib
import sys
from collections import Counter, defaultdict
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "artifacts/autogenesis/capability-gap-projection-v1.json"
FRONTIER_SCRIPT = ROOT / "scripts/fact-frontier.py"
CATALOG = ROOT / "artifacts/autogenesis/mathlib-nat-int-fact-catalog-v1.json"
CROSSWALK = ROOT / "artifacts/autogenesis/family-concept-crosswalk-v1.json"
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"


class CapabilityGapError(RuntimeError):
    """The authoritative frontier cannot be read safely."""


def frontier_module() -> Any:
    spec = importlib.util.spec_from_file_location("fact_frontier_for_capability_gap", FRONTIER_SCRIPT)
    if spec is None or spec.loader is None:
        raise CapabilityGapError(f"cannot load {FRONTIER_SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def build() -> dict[str, Any]:
    frontier = frontier_module()
    try:
        facts = frontier.load()
        machine = frontier.build_machine_frontier(facts)
    except (OSError, json.JSONDecodeError, KeyError, frontier.FrontierError) as error:
        raise CapabilityGapError(str(error)) from error

    entries = {entry["fact_id"]: entry for entry in machine["entries"]}
    try:
        catalog = json.loads(CATALOG.read_text())
        catalog_rows = catalog["facts"]
    except (OSError, json.JSONDecodeError, KeyError) as error:
        raise CapabilityGapError(f"cannot read reviewed fact catalog: {error}") from error
    catalog_by_fact = {
        row["fact_id"]: row for row in catalog_rows
        if isinstance(row, dict) and isinstance(row.get("fact_id"), str)
    }
    try:
        nursery = json.loads(NURSERY.read_text())
        partition_by_fact = {
            row["fact_id"]: row["partition"]
            for row in nursery["entries"]
            if isinstance(row, dict) and isinstance(row.get("fact_id"), str) and isinstance(row.get("partition"), str)
        }
    except (OSError, json.JSONDecodeError, KeyError) as error:
        raise CapabilityGapError(f"cannot read nursery partition manifest: {error}") from error
    evaluation_partitions = {"train", "development"}
    try:
        crosswalk = json.loads(CROSSWALK.read_text())
        concept_by_family = {
            row["family"]: row["concept_id"]
            for row in crosswalk["mappings"]
            if isinstance(row, dict)
        }
    except (OSError, json.JSONDecodeError, KeyError) as error:
        raise CapabilityGapError(f"cannot read reviewed family-concept crosswalk: {error}") from error
    rejected_by = {
        row["fact_id"]: row["rejected_by"]
        for row in machine["selection"]["rationale"]
    }
    ready = machine["selection"]["ready_fact_ids"]
    visible_ready = [fact_id for fact_id in ready if partition_by_fact.get(fact_id) in evaluation_partitions]
    held_out_ready = [fact_id for fact_id in ready if partition_by_fact.get(fact_id) == "held-out"]
    outside_ready = [fact_id for fact_id in ready if fact_id not in partition_by_fact]
    groups: dict[tuple[str, str, str], list[dict[str, Any]]] = defaultdict(list)
    for fact_id in visible_ready:
        entry = entries[fact_id]
        groups[(entry["formal_language"] if "formal_language" in entry else facts[fact_id]["formal"]["language"], entry["fragment"], entry["route_class"])].append(entry)

    rendered_groups = []
    for (language, fragment, route), rows in sorted(groups.items()):
        ready_ids = sorted(row["fact_id"] for row in rows)
        operation_ids = sorted({op for row in rows for op in row["registered_operation_ids"]})
        reasons = Counter(reason for row in rows for reason in rejected_by[row["fact_id"]])
        rendered_groups.append(
            {
                "formal_language": language,
                "fragment": fragment,
                "route_class": route,
                "ready_fact_ids": ready_ids,
                "ready_fact_count": len(ready_ids),
                "registered_operation_ids": operation_ids,
                "admissible_fact_ids": sorted(
                    fact_id for fact_id in ready_ids
                    if fact_id in machine["selection"]["admissible_fact_ids"]
                ),
                "rejection_reasons": [
                    {"reason": reason, "fact_count": reasons[reason]}
                    for reason in sorted(reasons)
                ],
            }
        )

    admissible = [fact_id for fact_id in machine["selection"]["admissible_fact_ids"] if fact_id in visible_ready]
    reasons = Counter(reason for fact_id in visible_ready for reason in rejected_by[fact_id])
    clusters: dict[tuple[str, str], list[str]] = defaultdict(list)
    for fact_id in visible_ready:
        row = catalog_by_fact.get(fact_id)
        if row is not None:
            clusters[(row["family"], row["statement_shape"])].append(fact_id)
    catalog_clusters = []
    for (family, statement_shape), fact_ids in sorted(clusters.items()):
        ids = sorted(fact_ids)
        components = sorted({catalog_by_fact[fact_id]["dependency_component_id"] for fact_id in ids})
        unlocked = sorted({child for fact_id in ids for child in entries[fact_id]["would_unlock"] if partition_by_fact.get(child) in evaluation_partitions})
        catalog_clusters.append(
            {
                "family": family,
                "statement_shape": statement_shape,
                "topic_concept_id": concept_by_family.get(family),
                "ready_fact_ids": ids,
                "ready_fact_count": len(ids),
                "dependency_component_ids": components,
                "direct_unlock_fact_ids": unlocked,
                "direct_unlock_fact_count": len(unlocked),
            }
        )
    cataloged = sorted(fact_id for fact_id in visible_ready if fact_id in catalog_by_fact)
    uncataloged = sorted(set(visible_ready).difference(cataloged))
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-capability-gap-projection",
        "derivation": {
            "source": "scripts/fact-frontier.py build_machine_frontier",
            "frontier_sha256": machine["frontier_sha256"],
            "ledger_sha256": machine["ledger"]["ledger_sha256"],
            "operation_registry_sha256": machine["policy"]["operation_registry_sha256"],
            "reviewed_fact_catalog_sha256": catalog.get("catalog_sha256"),
            "family_concept_crosswalk_path": str(CROSSWALK.relative_to(ROOT)),
            "nursery_sha256": hashlib.sha256(NURSERY.read_bytes()).hexdigest(),
            "evaluation_partitions": sorted(evaluation_partitions),
            "trust_boundary": "train/development ranking and producer-investigation input only; never held-out inspection, proof, or admission authority",
        },
        "census": {
            "global_dependency_ready_facts": len(ready),
            "excluded_held_out_ready_facts": len(held_out_ready),
            "excluded_outside_evaluation_ready_facts": len(outside_ready),
            "dependency_ready_facts": len(visible_ready),
            "admissible_facts": len(admissible),
            "groups": len(rendered_groups),
            "rejection_reasons": [
                {"reason": reason, "fact_count": reasons[reason]}
                for reason in sorted(reasons)
            ],
            "cataloged_ready_facts": len(cataloged),
            "uncataloged_ready_facts": len(uncataloged),
        },
        "groups": rendered_groups,
        "catalog_clusters": catalog_clusters,
        "uncataloged_ready_fact_ids": uncataloged,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        rendered = json.dumps(build(), indent=2, sort_keys=True) + "\n"
    except CapabilityGapError as error:
        print(f"AUTOGENESIS_CAPABILITY_GAP_ERROR|{error}", file=sys.stderr)
        return 1
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text() != rendered:
            print("AUTOGENESIS_CAPABILITY_GAP_ERROR|projection is stale", file=sys.stderr)
            return 1
    else:
        OUTPUT.write_text(rendered)
    data = json.loads(rendered)
    print(
        "AUTOGENESIS_CAPABILITY_GAP|"
        f"ready={data['census']['dependency_ready_facts']}|"
        f"admissible={data['census']['admissible_facts']}|"
        f"groups={data['census']['groups']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
