#!/usr/bin/env python3
"""Derive the shared and target-specific implementation slices for Nat.testBit."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict, deque
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
AUTO = ROOT / "artifacts/autogenesis"
GRAPH = AUTO / "imported-implementation-demand-v1.json"
REPLAY = AUTO / "retrieved-induction-type-slice-replay-v1.json"
DEMAND = AUTO / "semantic-contract-demand-v1.json"
OUTPUT = AUTO / "bit-observation-contract-slice-v1.json"
SOURCE = "Nat.testBit"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(graph: dict[str, Any], replay: dict[str, Any], demand: dict[str, Any]) -> dict[str, Any]:
    if graph.get("kind") != "axeyum-autogenesis-imported-implementation-demand":
        raise ValueError("wrong implementation graph")
    source_demand = [row for row in demand["demands"] if row["source_name"] == SOURCE]
    if len(source_demand) != 1 or source_demand[0]["affected_targets"] != 4:
        raise ValueError("Nat.testBit is not the reviewed four-target demand")
    fact_ids = source_demand[0]["affected_fact_ids"]
    replay_rows = {row["fact_id"]: row for row in replay["rows"]}
    if any(fact_id not in replay_rows for fact_id in fact_ids):
        raise ValueError("one affected fact has no checked type slice")
    roots = {
        (row["source_name"], row["source_content_sha256"]): row
        for row in graph["roots"]
    }
    nodes = {row["node_id"]: row for row in graph["nodes"]}
    edges = [(row["from_node_id"], row["to_node_id"]) for row in graph["edges"]]
    adjacency: dict[int, set[int]] = defaultdict(set)
    for source, target in edges:
        if nodes[target]["kind"] == "definition":
            adjacency[source].add(target)

    target_rows = []
    target_sets = []
    for fact_id in fact_ids:
        abstractions = replay_rows[fact_id]["receipt"]["abstractions"]
        root_keys = [
            (row["source_name"], row["source_content_sha256"])
            for row in abstractions
        ]
        if any(key not in roots for key in root_keys):
            raise ValueError(f"{fact_id} abstraction is absent from the graph")
        reachable = set().union(
            *(set(roots[key]["reachable_transparent_node_ids"]) for key in root_keys)
        )
        target_sets.append(reachable)
        target_rows.append(
            {
                "fact_id": fact_id,
                "source_names": [key[0] for key in root_keys],
                "reachable_transparent_nodes": len(reachable),
            }
        )
    shared = set.intersection(*target_sets)
    union = set.union(*target_sets)
    for row, reachable in zip(target_rows, target_sets, strict=True):
        row["target_specific_node_ids"] = sorted(reachable - shared)
        row["target_specific_nodes"] = len(reachable - shared)

    testbit_key = next(
        key for key in roots if key[0] == SOURCE
    )
    testbit_root_ids = [
        node_id
        for node_id in roots[testbit_key]["reachable_transparent_node_ids"]
        if nodes[node_id]["name"] == SOURCE
        and nodes[node_id]["content_sha256"] == testbit_key[1]
    ]
    if len(testbit_root_ids) != 1:
        raise ValueError("Nat.testBit graph root is ambiguous")
    distances = {testbit_root_ids[0]: 0}
    pending = deque(testbit_root_ids)
    while pending:
        current = pending.popleft()
        for child in sorted(adjacency[current]):
            if child not in distances:
                distances[child] = distances[current] + 1
                pending.append(child)
    shared_rows = [
        {
            "node_id": node_id,
            "name": nodes[node_id]["name"],
            "content_sha256": nodes[node_id]["content_sha256"],
            "dependency_sha256": nodes[node_id]["dependency_sha256"],
            "distance_from_testbit": distances.get(node_id),
        }
        for node_id in shared
    ]
    shared_rows.sort(
        key=lambda row: (
            row["distance_from_testbit"] is None,
            row["distance_from_testbit"] or 0,
            row["name"],
            row["node_id"],
        )
    )
    observation_tokens = ("testBit", "bitwise", "land", "lor", "shift", "ble", "decLe")
    observation_focus = [
        row for row in shared_rows if any(token in row["name"] for token in observation_tokens)
    ]
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-bit-observation-contract-slice",
        "state": "family-contract-design-context",
        "authority": "strategy context only; set intersection and lexical focus grant no semantic contract, proof, operation, applicability, transport, or fact-transition authority",
        "source": {
            "implementation_graph_sha256": digest(GRAPH),
            "type_slice_replay_sha256": digest(REPLAY),
            "semantic_contract_demand_sha256": digest(DEMAND),
            "selected_exact_source_name": SOURCE,
            "selection_rule": "the unique semantic-contract demand for Nat.testBit with four affected targets",
        },
        "census": {
            "targets": len(fact_ids),
            "union_transparent_nodes": len(union),
            "shared_transparent_nodes": len(shared),
            "observation_focus_nodes": len(observation_focus),
            "exact_axiom_free_behavior_candidates": source_demand[0]["exact_axiom_free_kernel_candidate_count"],
        },
        "targets": target_rows,
        "shared_nodes": shared_rows,
        "observation_focus": observation_focus,
        "behavior_candidates": source_demand[0]["exact_axiom_free_kernel_candidates"],
        "limitations": "The shared set is structural implementation overlap. The lexical observation focus is a review queue, not a contract vocabulary or semantic witness.",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    rendered = json.dumps(
        build(
            json.loads(GRAPH.read_text()),
            json.loads(REPLAY.read_text()),
            json.loads(DEMAND.read_text()),
        ),
        indent=2,
        sort_keys=True,
    ) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            print("BIT_OBSERVATION_CONTRACT_SLICE_ERROR|artifact is stale")
            return 1
    else:
        args.output.write_text(rendered)
    census = json.loads(rendered)["census"]
    print(
        "BIT_OBSERVATION_CONTRACT_SLICE|"
        f"targets={census['targets']}|shared={census['shared_transparent_nodes']}|"
        f"focus={census['observation_focus_nodes']}|candidates={census['exact_axiom_free_behavior_candidates']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
