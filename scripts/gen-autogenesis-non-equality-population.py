#!/usr/bin/env python3
"""Freeze the measured non-equality terminal stratum plus all false controls."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUTO = ROOT / "artifacts/autogenesis"
PROJECTION = AUTO / "retrieved-induction-obstruction-projection-v1.json"
OUTPUT = AUTO / "non-equality-terminal-population-v1.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(projection: dict) -> dict:
    positives = [
        row
        for row in projection.get("strategy_queue", [])
        if row.get("capability_demand") == "non-equality-terminal-family"
    ]
    controls = projection.get("control_observations", [])
    if len(positives) != 13 or len(controls) != 6:
        raise ValueError("non-equality stratum or control population changed")
    if any(
        row.get("evaluation_class") != "positive-target"
        or not row.get("eligible_for_strategy_queue")
        for row in positives
    ):
        raise ValueError("non-equality positive population is not strategy-eligible")
    if any(
        row.get("evaluation_class") != "must-decline-control"
        or row.get("eligible_for_strategy_queue")
        for row in controls
    ):
        raise ValueError("control population crossed the strategy boundary")
    rows = [
        {
            "fact_id": row["fact_id"],
            "target_definition": row["target_definition"],
        }
        for row in positives + controls
    ]
    rows.sort(key=lambda row: row["fact_id"])
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-non-equality-terminal-population",
        "state": "train-development-measurement-held-out-excluded",
        "source": {
            "projection_path": str(PROJECTION.relative_to(ROOT)),
            "projection_sha256": digest(PROJECTION),
        },
        "census": {
            "positive_targets": len(positives),
            "must_decline_controls": len(controls),
            "held_out_targets": 0,
        },
        "outcomes": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    rendered = json.dumps(build(json.loads(PROJECTION.read_text())), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            print("NON_EQUALITY_TERMINAL_POPULATION_ERROR|artifact is stale")
            return 1
    else:
        args.output.write_text(rendered)
    print("NON_EQUALITY_TERMINAL_POPULATION|positive=13|controls=6|held_out=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
