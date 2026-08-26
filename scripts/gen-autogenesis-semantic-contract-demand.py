#!/usr/bin/env python3
"""Join checked type-slice abstractions to exact kernel and contract evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from collections.abc import Iterator
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
AUTO = ROOT / "artifacts/autogenesis"
REPLAY = AUTO / "retrieved-induction-type-slice-replay-v1.json"
LEMMA_INDEX = AUTO / "kernel-lemma-search-index-v1.json"
OUTPUT = AUTO / "semantic-contract-demand-v1.json"
CONTRACT_SCHEMA = "axeyum-semantic-function-contract-receipt-v1"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def objects(value: Any) -> Iterator[dict[str, Any]]:
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from objects(child)
    elif isinstance(value, list):
        for child in value:
            yield from objects(child)


def registered_contracts() -> dict[str, list[dict[str, str]]]:
    found: dict[str, list[dict[str, str]]] = defaultdict(list)
    marker = CONTRACT_SCHEMA.encode()
    for path in sorted(AUTO.glob("*.json")):
        if path == OUTPUT:
            continue
        data = path.read_bytes()
        if marker not in data:
            continue
        for value in objects(json.loads(data)):
            if value.get("schema_version") != CONTRACT_SCHEMA:
                continue
            source = value.get("source", {})
            source_hash = source.get("content_sha256")
            if isinstance(source_hash, str):
                found[source_hash].append(
                    {
                        "artifact_path": str(path.relative_to(ROOT)),
                        "receipt_sha256": value.get("receipt_sha256", ""),
                        "source_name": source.get("name", ""),
                    }
                )
    return found


def build(replay: dict[str, Any], lemma_index: dict[str, Any]) -> dict[str, Any]:
    if (
        replay.get("kind") != "axeyum-autogenesis-checked-type-slice-replay"
        or replay.get("coverage") != {"accepted-receipt": 25}
        or replay.get("population_selection", {}).get("target_outcomes_accessed")
        is not True
    ):
        raise ValueError("input is not the checked outcome-selected type-slice replay")
    if lemma_index.get("kind") != "axeyum-kernel-lemma-search-index":
        raise ValueError("input is not the kernel lemma-search index")
    groups: dict[tuple[str, str], dict[str, Any]] = {}
    for row in replay["rows"]:
        if row.get("outcome") != "accepted-receipt":
            raise ValueError("type-slice replay contains a non-accepted row")
        for abstraction in row["receipt"]["abstractions"]:
            name = abstraction["source_name"]
            source_hash = abstraction["source_content_sha256"]
            key = (name, source_hash)
            group = groups.setdefault(
                key,
                {
                    "source_name": name,
                    "source_content_sha256": source_hash,
                    "source_type_sha256": abstraction["instantiated_type_sha256"],
                    "fact_ids": set(),
                    "partitions": set(),
                    "source_occurrences": 0,
                },
            )
            if group["source_type_sha256"] != abstraction["instantiated_type_sha256"]:
                raise ValueError(f"one source identity has inconsistent types: {name}")
            group["fact_ids"].add(row["fact_id"])
            group["partitions"].add(row["partition"])
            group["source_occurrences"] += abstraction["source_occurrences"]
    contracts = registered_contracts()
    demands = []
    for (_name, source_hash), group in groups.items():
        candidates = [
            {
                "kernel_declaration_id": lemma["kernel_declaration_id"],
                "canonical_type": lemma["canonical_type"],
                "exact_fact_ids": lemma["exact_fact_ids"],
                "direct_theorem_dependencies": lemma["direct_theorem_dependencies"],
            }
            for lemma in lemma_index["lemmas"]
            if lemma["axiom_footprint_size"] == 0
            and group["source_name"] in lemma["direct_type_dependencies"]
        ]
        candidates.sort(key=lambda row: row["kernel_declaration_id"])
        receipts = sorted(
            contracts.get(source_hash, []), key=lambda row: row["artifact_path"]
        )
        facts = sorted(group["fact_ids"])
        if receipts:
            next_action = "producer-integration"
        elif candidates:
            next_action = "construct-and-check-generic-contract"
        else:
            next_action = "find-or-construct-behavior-theorems"
        demands.append(
            {
                "source_name": group["source_name"],
                "source_content_sha256": source_hash,
                "source_type_sha256": group["source_type_sha256"],
                "affected_fact_ids": facts,
                "affected_targets": len(facts),
                "partitions": sorted(group["partitions"]),
                "source_occurrences": group["source_occurrences"],
                "checked_contract_receipts": receipts,
                "checked_contract_receipt_count": len(receipts),
                "exact_axiom_free_kernel_candidates": candidates,
                "exact_axiom_free_kernel_candidate_count": len(candidates),
                "next_action": next_action,
                "strategy_eligible": True,
            }
        )
    demands.sort(
        key=lambda row: (
            -int(row["checked_contract_receipt_count"] > 0),
            -int(row["exact_axiom_free_kernel_candidate_count"] > 0),
            -row["affected_targets"],
            row["source_name"],
        )
    )
    for rank, row in enumerate(demands, 1):
        row["strategy_rank"] = rank
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-semantic-contract-demand",
        "state": "candidate-only-exact-identity-join",
        "authority": "strategy context only; no contract, proof, operation, applicability, or fact-transition authority",
        "source": {
            "type_slice_replay_path": str(REPLAY.relative_to(ROOT)),
            "type_slice_replay_sha256": digest(REPLAY),
            "lemma_index_path": str(LEMMA_INDEX.relative_to(ROOT)),
            "lemma_index_sha256": digest(LEMMA_INDEX),
            "contract_receipt_schema_scanned": CONTRACT_SCHEMA,
            "contract_artifact_scope": "artifacts/autogenesis/*.json",
        },
        "census": {
            "accepted_type_slices": 25,
            "distinct_source_identities": len(demands),
            "identities_with_checked_contract_receipts": sum(
                row["checked_contract_receipt_count"] > 0 for row in demands
            ),
            "identities_with_exact_kernel_candidates": sum(
                row["exact_axiom_free_kernel_candidate_count"] > 0 for row in demands
            ),
            "exact_axiom_free_kernel_candidates": sum(
                row["exact_axiom_free_kernel_candidate_count"] for row in demands
            ),
        },
        "demands": demands,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    rendered = json.dumps(
        build(json.loads(REPLAY.read_text()), json.loads(LEMMA_INDEX.read_text())),
        indent=2,
        sort_keys=True,
    ) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            print("SEMANTIC_CONTRACT_DEMAND_ERROR|artifact is stale")
            return 1
    else:
        args.output.write_text(rendered)
    census = json.loads(rendered)["census"]
    print(
        "SEMANTIC_CONTRACT_DEMAND|"
        f"identities={census['distinct_source_identities']}|"
        f"with_receipts={census['identities_with_checked_contract_receipts']}|"
        f"with_candidates={census['identities_with_exact_kernel_candidates']}|"
        f"candidates={census['exact_axiom_free_kernel_candidates']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
