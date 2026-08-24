#!/usr/bin/env python3
"""Validate the candidate-capability demand projection against its sources."""

from __future__ import annotations

import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AUTO = ROOT / "artifacts/autogenesis"
PATH = AUTO / "capability-candidate-demand-v1.json"


def validate(data: dict) -> list[str]:
    errors: list[str] = []
    if data.get("kind") != "axeyum-capability-candidate-demand":
        return ["invalid projection kind"]
    overlay = json.loads((AUTO / "knowledge-overlay-v1.json").read_text())
    obstruction_doc = json.loads((AUTO / "obstruction-projection-v1.json").read_text())
    candidates = {
        entity["id"]: entity
        for entity in overlay["entities"]
        if entity["kind"] == "capability" and entity["status"] == "candidate"
    }
    obstructions = {obstruction["id"]: obstruction for obstruction in obstruction_doc["obstructions"]}
    rows = data.get("candidates", [])
    seen: set[str] = set()
    families = episodes = 0
    keys = []
    for row in rows:
        identifier = row.get("capability_id")
        if identifier not in candidates or identifier in seen:
            errors.append(f"{identifier}: candidate capability is absent or duplicated")
            continue
        seen.add(identifier)
        ids = row.get("obstruction_ids", [])
        matched = [obstructions.get(identifier_) for identifier_ in ids]
        if not ids or any(obstruction is None for obstruction in matched):
            errors.append(f"{identifier}: obstruction identifiers are invalid")
            continue
        expected = [
            obstruction for obstruction in obstructions.values()
            if obstruction.get("candidate_capability") == identifier
        ]
        if sorted(ids) != sorted(obstruction["id"] for obstruction in expected):
            errors.append(f"{identifier}: obstruction set does not exactly match source projection")
        expected_families = len(expected)
        expected_episodes = sum(obstruction["affected_population"]["episodes"] for obstruction in expected)
        expected_categories = sorted({category for obstruction in expected for category in obstruction["complete_known_blocker_set"]})
        if row.get("affected_obstruction_families") != expected_families:
            errors.append(f"{identifier}: obstruction-family count disagrees")
        if row.get("affected_episodes") != expected_episodes:
            errors.append(f"{identifier}: episode count disagrees")
        if row.get("observed_blocker_categories") != expected_categories:
            errors.append(f"{identifier}: blocker categories disagree")
        if row.get("overlay_status") != "candidate":
            errors.append(f"{identifier}: overlay status is not candidate")
        families += expected_families
        episodes += expected_episodes
        keys.append((-expected_families, -expected_episodes, identifier))
    if keys != sorted(keys):
        errors.append("candidate rows are not in deterministic demand order")
    census = data.get("census", {})
    if (census.get("candidate_capabilities_with_measured_demand"), census.get("affected_obstruction_families"), census.get("affected_episodes")) != (len(rows), families, episodes):
        errors.append("demand census disagrees with candidate rows")
    return errors


def main() -> int:
    errors = validate(json.loads(PATH.read_text()))
    for error in errors:
        print(f"AUTOGENESIS_CAPABILITY_DEMAND_ERROR|{error}", file=sys.stderr)
    if errors:
        return 1
    print("AUTOGENESIS_CAPABILITY_DEMAND_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
