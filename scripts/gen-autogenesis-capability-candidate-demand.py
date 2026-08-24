#!/usr/bin/env python3
"""Derive an investigation-only demand view for candidate capabilities."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AUTO = ROOT / "artifacts/autogenesis"
OVERLAY = AUTO / "knowledge-overlay-v1.json"
OBSTRUCTIONS = AUTO / "obstruction-projection-v1.json"
OUTPUT = AUTO / "capability-candidate-demand-v1.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build() -> dict:
    overlay = json.loads(OVERLAY.read_text())
    obstructions = json.loads(OBSTRUCTIONS.read_text())
    entities = {
        entity["id"]: entity
        for entity in overlay["entities"]
        if entity["kind"] == "capability" and entity["status"] == "candidate"
    }
    grouped: dict[str, list[dict]] = {identifier: [] for identifier in entities}
    for obstruction in obstructions["obstructions"]:
        identifier = obstruction["candidate_capability"]
        if identifier in grouped:
            grouped[identifier].append(obstruction)
    rows = []
    for identifier, matched in grouped.items():
        if not matched:
            continue
        categories = sorted(
            {category for obstruction in matched for category in obstruction["complete_known_blocker_set"]}
        )
        episodes = sum(obstruction["affected_population"]["episodes"] for obstruction in matched)
        rows.append(
            {
                "capability_id": identifier,
                "title": entities[identifier]["title"],
                "overlay_status": "candidate",
                "obstruction_ids": sorted(obstruction["id"] for obstruction in matched),
                "affected_obstruction_families": len(matched),
                "affected_episodes": episodes,
                "observed_blocker_categories": categories,
                "ranking_basis": "distinct retained obstruction families, then affected retained episodes; no proof, implementation, or admission authority",
            }
        )
    rows.sort(key=lambda row: (-row["affected_obstruction_families"], -row["affected_episodes"], row["capability_id"]))
    return {
        "schema_version": 1,
        "kind": "axeyum-capability-candidate-demand",
        "derivation": {
            "knowledge_overlay_sha256": sha(OVERLAY),
            "obstruction_projection_sha256": sha(OBSTRUCTIONS),
            "candidate_rule": "overlay capability entity with status candidate and at least one obstruction candidate_capability reference",
            "trust_boundary": "investigation ranking only; never producer selection, proof construction, admission, or trust authority",
        },
        "census": {
            "candidate_capabilities_with_measured_demand": len(rows),
            "affected_obstruction_families": sum(row["affected_obstruction_families"] for row in rows),
            "affected_episodes": sum(row["affected_episodes"] for row in rows),
        },
        "candidates": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text() != rendered:
            print("AUTOGENESIS_CAPABILITY_DEMAND_ERROR|projection is stale", file=sys.stderr)
            return 1
    else:
        OUTPUT.write_text(rendered)
    census = json.loads(rendered)["census"]
    print(
        "AUTOGENESIS_CAPABILITY_DEMAND|"
        f"candidates={census['candidate_capabilities_with_measured_demand']}|"
        f"families={census['affected_obstruction_families']}|"
        f"episodes={census['affected_episodes']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
