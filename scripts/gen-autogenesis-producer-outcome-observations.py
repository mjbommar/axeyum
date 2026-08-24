#!/usr/bin/env python3
"""Derive outcome-safe producer observations from the sealed train/dev census.

The output is deliberately descriptive.  It neither registers an operation nor
marks a fact admissible: it is a hash-bound view of one fixed producer run,
partitioned by reviewed fact-family and statement shape.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from collections import Counter, defaultdict
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
AUTO = ROOT / "artifacts" / "autogenesis"
OUT = AUTO / "producer-outcome-observations-v1.json"
CENSUS = AUTO / "mathlib-type-slice-producer-census-v1.json"
CATALOG = AUTO / "mathlib-nat-int-fact-catalog-v1.json"


class ObservationError(RuntimeError):
    """A pinned input is absent or cannot support an outcome observation."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: pathlib.Path, label: str) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise ObservationError(f"cannot read {label}: {error}") from error
    if not isinstance(data, dict):
        raise ObservationError(f"{label} is not an object")
    return data


def build() -> dict[str, Any]:
    census = load_json(CENSUS, "producer census manifest")
    catalog = load_json(CATALOG, "reviewed fact catalog")
    observation_meta = census.get("observation_archive")
    source_meta = census.get("source_archive")
    if not isinstance(observation_meta, dict) or not isinstance(source_meta, dict):
        raise ObservationError("producer census lacks pinned archive metadata")
    observation_path = pathlib.Path(observation_meta.get("root", "")) / str(observation_meta.get("file", ""))
    mapping_path = pathlib.Path(source_meta.get("root", "")) / "mapping.json"
    if not observation_path.is_file() or not mapping_path.is_file():
        raise ObservationError("pinned observation or mapping archive is unavailable")
    if sha256(observation_path) != observation_meta.get("file_sha256"):
        raise ObservationError("observation archive digest disagrees with census manifest")
    if sha256(mapping_path) != source_meta.get("mapping_sha256"):
        raise ObservationError("mapping archive digest disagrees with census manifest")
    observation = load_json(observation_path, "pinned producer observation")
    mapping = load_json(mapping_path, "pinned source mapping")
    if observation.get("observation_sha256") != observation_meta.get("observation_sha256"):
        raise ObservationError("observation semantic identity disagrees with census manifest")
    if observation.get("mapping_sha256") != source_meta.get("mapping_sha256"):
        raise ObservationError("observation mapping identity disagrees with census manifest")
    rows = observation.get("rows")
    mapped_rows = mapping.get("rows")
    if not isinstance(rows, list) or not isinstance(mapped_rows, list):
        raise ObservationError("observation or mapping rows are missing")
    by_target = {
        row.get("target_definition"): row
        for row in mapped_rows
        if isinstance(row, dict) and isinstance(row.get("target_definition"), str)
    }
    if len(by_target) != len(mapped_rows):
        raise ObservationError("mapping target definitions are not unique")
    catalog_by_fact = {
        row.get("fact_id"): row
        for row in catalog.get("facts", [])
        if isinstance(row, dict) and isinstance(row.get("fact_id"), str)
    }
    rendered_rows: list[dict[str, Any]] = []
    outcomes: Counter[str] = Counter()
    partitions: Counter[str] = Counter()
    for row in rows:
        if not isinstance(row, dict):
            raise ObservationError("observation has a non-object row")
        target = row.get("target_definition")
        mapped = by_target.get(target)
        if mapped is None:
            raise ObservationError(f"observation target is absent from mapping: {target!r}")
        fact_id, family, partition, outcome = (mapped.get("fact_id"), mapped.get("family"), mapped.get("partition"), row.get("outcome"))
        if not all(isinstance(value, str) and value for value in (fact_id, family, partition, outcome)):
            raise ObservationError("row lacks fact, family, partition, or outcome")
        if partition not in {"train", "development"}:
            raise ObservationError(f"outcome row is outside train/development: {partition}")
        catalog_row = catalog_by_fact.get(fact_id)
        if catalog_row is None or catalog_row.get("family") != family:
            raise ObservationError(f"outcome row lacks matching reviewed catalog family: {fact_id}")
        receipt = row.get("receipt")
        abstractions = receipt.get("abstractions") if isinstance(receipt, dict) else None
        if not isinstance(abstractions, list):
            raise ObservationError(f"outcome row lacks receipt abstractions: {fact_id}")
        abstraction_class = "exact-source" if not abstractions else "semantic-abstraction"
        rendered_rows.append({
            "fact_id": fact_id,
            "family": family,
            "statement_shape": catalog_row.get("statement_shape"),
            "partition": partition,
            "outcome": outcome,
            "abstraction_class": abstraction_class,
            "definition_abstraction_count": len(abstractions),
        })
        outcomes[outcome] += 1
        partitions[partition] += 1
    if len(rendered_rows) != len(by_target) or len({row["fact_id"] for row in rendered_rows}) != len(rendered_rows):
        raise ObservationError("observation does not have one unique row per mapped fact")
    expected = census.get("coverage")
    if dict(sorted(outcomes.items())) != expected:
        raise ObservationError("outcomes disagree with producer census coverage")
    if sum(partitions.values()) != census.get("population", {}).get("train_development"):
        raise ObservationError("population disagrees with producer census")
    grouped: dict[tuple[str, str, str, str], list[str]] = defaultdict(list)
    for row in rendered_rows:
        shape = row["statement_shape"]
        if not isinstance(shape, str) or not shape:
            raise ObservationError(f"catalog statement shape missing for {row['fact_id']}")
        grouped[(row["family"], shape, row["abstraction_class"], row["outcome"])].append(row["fact_id"])
    groups = [
        {
            "family": family,
            "statement_shape": shape,
            "abstraction_class": abstraction_class,
            "outcome": outcome,
            "observed_fact_ids": sorted(ids),
            "observed_fact_count": len(ids),
        }
        for (family, shape, abstraction_class, outcome), ids in sorted(grouped.items())
    ]
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-producer-outcome-observations",
        "derivation": {
            "producer_census_manifest_sha256": sha256(CENSUS),
            "reviewed_fact_catalog_sha256": sha256(CATALOG),
            "observation_file_sha256": observation_meta["file_sha256"],
            "observation_sha256": observation_meta["observation_sha256"],
            "mapping_sha256": source_meta["mapping_sha256"],
            "partitions": ["development", "train"],
            "trust_boundary": "train/development diagnostic observations only; never held-out evaluation, operation registration, proof, admission, or scheduling authority",
        },
        "producer": census.get("producer"),
        "census": {
            "observed_facts": len(rendered_rows),
            "held_out_observed_facts": 0,
            "partitions": dict(sorted(partitions.items())),
            "outcomes": dict(sorted(outcomes.items())),
            "exact_source_facts": sum(row["abstraction_class"] == "exact-source" for row in rendered_rows),
            "semantic_abstraction_facts": sum(row["abstraction_class"] == "semantic-abstraction" for row in rendered_rows),
            "groups": len(groups),
        },
        "groups": groups,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        rendered = json.dumps(build(), indent=2, sort_keys=True) + "\n"
    except ObservationError as error:
        print(f"AUTOGENESIS_PRODUCER_OUTCOMES_ERROR|{error}", file=sys.stderr)
        return 1
    if args.check:
        if not OUT.is_file() or OUT.read_text() != rendered:
            print("AUTOGENESIS_PRODUCER_OUTCOMES_ERROR|projection is stale", file=sys.stderr)
            return 1
    else:
        OUT.write_text(rendered)
    data = json.loads(rendered)
    print(
        "AUTOGENESIS_PRODUCER_OUTCOMES|"
        f"facts={data['census']['observed_facts']}|"
        f"held_out={data['census']['held_out_observed_facts']}|"
        f"groups={data['census']['groups']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
