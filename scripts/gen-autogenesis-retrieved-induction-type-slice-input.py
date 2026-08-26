#!/usr/bin/env python3
"""Build the held-out-safe type-slice population from measured import blockers."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
AUTO = ROOT / "artifacts/autogenesis"
PROJECTION = AUTO / "retrieved-induction-obstruction-projection-v1.json"
NURSERY = AUTO / "nursery-v1.json"
OUTPUT = AUTO / "retrieved-induction-type-slice-input-v1.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(projection: dict[str, Any], nursery: dict[str, Any]) -> dict[str, Any]:
    if projection.get("kind") != "axeyum-retrieved-induction-obstruction-projection":
        raise ValueError("input is not the retrieved-induction obstruction projection")
    partitions = {
        row["fact_id"]: row
        for row in nursery.get("entries", [])
        if isinstance(row, dict) and isinstance(row.get("fact_id"), str)
    }
    rows = []
    for source in projection.get("strategy_queue", []):
        if source.get("capability_demand") != "type-slice-generalization":
            continue
        fact_id = source["fact_id"]
        if source.get("evaluation_class") != "positive-target" or not source.get(
            "eligible_for_strategy_queue"
        ):
            raise ValueError(f"type-slice target is not strategy-eligible: {fact_id}")
        nursery_row = partitions.get(fact_id)
        if nursery_row is None:
            raise ValueError(f"type-slice target is absent from nursery: {fact_id}")
        partition = nursery_row.get("partition")
        if partition not in {"train", "development"}:
            raise ValueError(f"type-slice target is not unsealed: {fact_id}")
        rows.append(
            {
                "artifact_file": f"{fact_id.replace(':', '-', 1)}.ndjson",
                "fact_id": fact_id,
                "family": nursery_row.get("family"),
                "partition": partition,
                "target_definition": source["target_definition"],
                "source_obstruction": source["reason_kind"],
            }
        )
    rows.sort(key=lambda row: row["fact_id"])
    if len(rows) != 25:
        raise ValueError(f"expected 25 measured type-slice targets, found {len(rows)}")
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-retrieved-induction-type-slice-input",
        "state": "proof-free-source-input",
        "authority": {
            "partitions_inspected": ["development", "train"],
            "held_out_inspected": False,
            "proof_bodies_accessed": False,
            "target_outcomes_accessed": True,
            "facts_opened": len(rows),
            "ledger_writes": 0,
        },
        "source": {
            "projection_path": str(PROJECTION.relative_to(ROOT)),
            "projection_sha256": digest(PROJECTION),
            "nursery_path": str(NURSERY.relative_to(ROOT)),
            "nursery_sha256": digest(NURSERY),
        },
        "rows": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    rendered = json.dumps(
        build(json.loads(PROJECTION.read_text()), json.loads(NURSERY.read_text())),
        indent=2,
        sort_keys=True,
    ) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            print("RETRIEVED_INDUCTION_TYPE_SLICE_INPUT_ERROR|artifact is stale")
            return 1
    else:
        args.output.write_text(rendered)
    print("RETRIEVED_INDUCTION_TYPE_SLICE_INPUT|targets=25|held_out=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
