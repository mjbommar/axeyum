#!/usr/bin/env python3
"""Project the clean bitwise family onto its pinned Mathlib sibling facts."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEMAND = ROOT / "artifacts/autogenesis/bitwise-semantic-law-demand-v1.json"
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
OUTPUT = ROOT / "artifacts/autogenesis/bitwise-clean-family-projection-v1.json"
MAPPINGS = [
    (
        "F:ml430-nat-testbit-land-dfef7ca4",
        "bitwiseAnd",
        "boolAnd",
        "testBitBool_bitwiseAnd",
    ),
    (
        "F:ml430-nat-testbit-lor-7644e067",
        "bitwiseOr",
        "boolOr",
        "testBitBool_bitwiseOr",
    ),
    (
        "F:ml430-nat-testbit-ldiff-16f94162",
        "bitwiseDifference",
        "boolDifference",
        "testBitBool_bitwiseDifference",
    ),
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fact_path(fact_id: str) -> Path:
    return ROOT / "artifacts/facts" / f"{fact_id.replace(':', '-')}.json"


def build() -> dict[str, Any]:
    demand = json.loads(DEMAND.read_text())
    specializations = {
        row["theorem"].rsplit(".", 1)[-1]: row
        for row in demand["native_reification"]["total_bitwise_specializations"]
    }
    nursery = json.loads(NURSERY.read_text())
    partitions = {row["fact_id"]: row for row in nursery["entries"]}
    rows = []
    fact_sources = []
    for fact_id, operation, boolean_operation, theorem in MAPPINGS:
        path = fact_path(fact_id)
        fact = json.loads(path.read_text())
        nursery_row = partitions.get(fact_id)
        specialization = specializations.get(theorem)
        if fact.get("epistemic_status") != "open":
            raise ValueError(f"{fact_id} is no longer an open projection target")
        if nursery_row is None or nursery_row.get("partition") != "development":
            raise ValueError(f"{fact_id} left the development partition")
        if specialization is None or specialization.get("axiom_footprint_size") != 0:
            raise ValueError(f"clean specialization is absent or assumption-bearing: {theorem}")
        if operation not in specialization.get("canonical_type", ""):
            raise ValueError(f"clean specialization type does not name {operation}")
        rows.append(
            {
                "fact_id": fact_id,
                "fact_statement": fact["formal"]["statement"],
                "partition": nursery_row["partition"],
                "family": nursery_row["family"],
                "clean_operation": f"Axeyum.Autogenesis.{operation}",
                "clean_boolean_operation": f"Axeyum.Autogenesis.{boolean_operation}",
                "clean_theorem": f"Axeyum.Autogenesis.{theorem}",
                "clean_canonical_type": specialization["canonical_type"],
                "clean_axiom_footprint_size": 0,
                "generic_theorem_dependency": specialization[
                    "generic_theorem_dependency"
                ],
                "relationship": "target-owned-semantic-analogue",
                "exact_imported_identity": False,
                "authoritative_operation_eligible": False,
                "blocking_obligations": [
                    "exact-imported-testBit-equivalence",
                    "exact-imported-operation-equivalence",
                    "imported-definition-propext-floor",
                ],
            }
        )
        fact_sources.append(
            {"path": str(path.relative_to(ROOT)), "sha256": digest(path)}
        )
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-bitwise-clean-family-projection",
        "state": "clean-three-sibling-family-exact-imported-admission-blocked",
        "authority": "knowledge projection only; no exact operation identity, no proof transport, no operation registration, no theorem admission, and no fact-transition authority",
        "source": {
            "semantic_demand": {
                "path": str(DEMAND.relative_to(ROOT)),
                "sha256": digest(DEMAND),
            },
            "nursery": {"path": str(NURSERY.relative_to(ROOT)), "sha256": digest(NURSERY)},
            "facts": fact_sources,
        },
        "census": {
            "development_targets": len(rows),
            "clean_axiom_free_analogues": len(rows),
            "exact_imported_matches": 0,
            "authoritative_operation_eligible": 0,
        },
        "rows": rows,
        "next": "promote the target-owned family as its own reusable library surface and fact identities, or explicitly authorize a separately labeled weaker imported-definition route; do not close these exact Mathlib facts from semantic analogy",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    rendered = json.dumps(build(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            print("BITWISE_CLEAN_FAMILY_PROJECTION_ERROR|artifact is stale")
            return 1
    else:
        args.output.write_text(rendered)
    census = json.loads(rendered)["census"]
    print(
        "BITWISE_CLEAN_FAMILY_PROJECTION|"
        f"targets={census['development_targets']}|"
        f"clean_analogues={census['clean_axiom_free_analogues']}|"
        f"exact_matches={census['exact_imported_matches']}|"
        f"operation_eligible={census['authoritative_operation_eligible']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
