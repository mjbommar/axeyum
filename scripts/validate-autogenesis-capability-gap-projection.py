#!/usr/bin/env python3
"""Validate internal accounting for the derived capability-gap projection."""

from __future__ import annotations

import json
import pathlib
import sys
from collections import Counter
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PATH = ROOT / "artifacts/autogenesis/capability-gap-projection-v1.json"


def validate(data: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if data.get("kind") != "axeyum-autogenesis-capability-gap-projection":
        return ["invalid projection kind"]
    if data.get("schema_version") != 1:
        errors.append("invalid schema version")
    derivation = data.get("derivation")
    if not isinstance(derivation, dict) or not all(
        isinstance(derivation.get(key), str) and derivation[key]
        for key in ("frontier_sha256", "ledger_sha256", "operation_registry_sha256", "reviewed_fact_catalog_sha256", "trust_boundary")
    ):
        errors.append("missing source identities or trust boundary")
    groups = data.get("groups")
    if not isinstance(groups, list):
        return errors + ["groups must be a list"]
    all_ready: list[str] = []
    all_admissible: list[str] = []
    group_keys: list[tuple[str, str, str]] = []
    group_reasons: Counter[str] = Counter()
    for group in groups:
        if not isinstance(group, dict):
            errors.append("group is not an object")
            continue
        key = tuple(group.get(field) for field in ("formal_language", "fragment", "route_class"))
        if not all(isinstance(part, str) and part for part in key):
            errors.append("group has invalid typed surface")
        group_keys.append(key)  # type: ignore[arg-type]
        ready = group.get("ready_fact_ids")
        admissible = group.get("admissible_fact_ids")
        operations = group.get("registered_operation_ids")
        reasons = group.get("rejection_reasons")
        if not isinstance(ready, list) or ready != sorted(set(ready)):
            errors.append(f"{key}: ready facts must be sorted and unique")
            continue
        if group.get("ready_fact_count") != len(ready):
            errors.append(f"{key}: ready fact count disagrees with ids")
        if not isinstance(admissible, list) or not set(admissible).issubset(ready):
            errors.append(f"{key}: admissible facts are not a ready subset")
        if not isinstance(operations, list) or operations != sorted(set(operations)):
            errors.append(f"{key}: operations must be sorted and unique")
        if not isinstance(reasons, list):
            errors.append(f"{key}: rejection reasons must be a list")
        else:
            for reason in reasons:
                if not isinstance(reason, dict) or not isinstance(reason.get("reason"), str) or not isinstance(reason.get("fact_count"), int) or reason["fact_count"] <= 0:
                    errors.append(f"{key}: invalid rejection reason")
                else:
                    group_reasons[reason["reason"]] += reason["fact_count"]
        all_ready.extend(ready)
        all_admissible.extend(admissible if isinstance(admissible, list) else [])
    if group_keys != sorted(set(group_keys)):
        errors.append("groups are not uniquely sorted by typed surface")
    if len(all_ready) != len(set(all_ready)):
        errors.append("a ready fact appears in more than one group")
    if len(all_admissible) != len(set(all_admissible)):
        errors.append("an admissible fact appears in more than one group")
    census = data.get("census", {})
    if census.get("dependency_ready_facts") != len(all_ready):
        errors.append("ready census disagrees with groups")
    if census.get("admissible_facts") != len(all_admissible):
        errors.append("admissible census disagrees with groups")
    if census.get("groups") != len(groups):
        errors.append("group census disagrees with groups")
    expected_reasons = [
        {"reason": reason, "fact_count": group_reasons[reason]}
        for reason in sorted(group_reasons)
    ]
    if census.get("rejection_reasons") != expected_reasons:
        errors.append("rejection-reason census disagrees with groups")
    catalog_clusters = data.get("catalog_clusters")
    uncataloged = data.get("uncataloged_ready_fact_ids")
    if not isinstance(catalog_clusters, list) or not isinstance(uncataloged, list):
        return errors + ["catalog clusters and uncataloged facts must be lists"]
    cataloged_ids: list[str] = []
    cluster_keys: list[tuple[str, str]] = []
    for cluster in catalog_clusters:
        if not isinstance(cluster, dict):
            errors.append("catalog cluster is not an object")
            continue
        key = (cluster.get("family"), cluster.get("statement_shape"))
        if not all(isinstance(part, str) and part for part in key):
            errors.append("catalog cluster has invalid family or shape")
        cluster_keys.append(key)  # type: ignore[arg-type]
        ids = cluster.get("ready_fact_ids")
        components = cluster.get("dependency_component_ids")
        if not isinstance(ids, list) or ids != sorted(set(ids)):
            errors.append(f"{key}: catalog facts must be sorted and unique")
            continue
        if cluster.get("ready_fact_count") != len(ids):
            errors.append(f"{key}: catalog count disagrees with ids")
        if not isinstance(components, list) or components != sorted(set(components)):
            errors.append(f"{key}: dependency components must be sorted and unique")
        cataloged_ids.extend(ids)
    if cluster_keys != sorted(set(cluster_keys)):
        errors.append("catalog clusters are not uniquely sorted")
    if len(cataloged_ids) != len(set(cataloged_ids)):
        errors.append("a cataloged fact appears in more than one cluster")
    if not set(cataloged_ids).issubset(all_ready):
        errors.append("cataloged fact is not dependency-ready")
    if not isinstance(uncataloged, list) or uncataloged != sorted(set(uncataloged)):
        errors.append("uncataloged facts must be sorted and unique")
    elif set(uncataloged).intersection(cataloged_ids) or set(uncataloged).union(cataloged_ids) != set(all_ready):
        errors.append("cataloged and uncataloged facts do not partition ready facts")
    if census.get("cataloged_ready_facts") != len(cataloged_ids):
        errors.append("cataloged-ready census disagrees with clusters")
    if census.get("uncataloged_ready_facts") != len(uncataloged):
        errors.append("uncataloged-ready census disagrees with ids")
    return errors


def main() -> int:
    try:
        data = json.loads(PATH.read_text())
    except (OSError, json.JSONDecodeError) as error:
        print(f"AUTOGENESIS_CAPABILITY_GAP_ERROR|cannot read projection: {error}", file=sys.stderr)
        return 1
    errors = validate(data)
    for error in errors:
        print(f"AUTOGENESIS_CAPABILITY_GAP_ERROR|{error}", file=sys.stderr)
    if errors:
        return 1
    print(
        "AUTOGENESIS_CAPABILITY_GAP_OK|"
        f"ready={data['census']['dependency_ready_facts']}|"
        f"admissible={data['census']['admissible_facts']}|"
        f"groups={data['census']['groups']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
