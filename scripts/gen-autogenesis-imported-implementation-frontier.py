#!/usr/bin/env python3
"""Project imported implementation edges into reverse contract reachability."""

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
DEMAND = AUTO / "semantic-contract-demand-v1.json"
OUTPUT = AUTO / "imported-implementation-frontier-v1.json"

Identity = int


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(graph: dict[str, Any], demand: dict[str, Any]) -> dict[str, Any]:
    if graph.get("kind") != "axeyum-autogenesis-imported-implementation-demand":
        raise ValueError("input is not the imported implementation-demand graph")
    if demand.get("kind") != "axeyum-autogenesis-semantic-contract-demand":
        raise ValueError("input is not semantic-contract demand")
    all_nodes = {row["node_id"]: row for row in graph["nodes"]}
    if len(all_nodes) != len(graph["nodes"]):
        raise ValueError("declaration node IDs are duplicated")
    nodes = {node_id: row for node_id, row in all_nodes.items() if row["kind"] == "definition"}
    adjacency: dict[Identity, set[Identity]] = defaultdict(set)
    reverse: dict[Identity, set[Identity]] = defaultdict(set)
    for edge in graph["edges"]:
        source = edge["from_node_id"]
        target = edge["to_node_id"]
        if source not in nodes:
            raise ValueError("edge source is absent")
        if all_nodes[target]["kind"] == "definition":
            adjacency[source].add(target)
            reverse[target].add(source)
    demand_by_root = {
        (row["source_name"], row["source_content_sha256"]): row
        for row in demand["demands"]
    }
    roots = {
        (row["source_name"], row["source_content_sha256"]): row
        for row in graph["roots"]
    }
    if set(roots) != set(demand_by_root):
        raise ValueError("graph roots and semantic demands differ")

    root_distances: dict[Identity, dict[tuple[str, str], int]] = defaultdict(dict)
    for root in sorted(roots):
        expected = set(roots[root]["reachable_transparent_node_ids"])
        root_matches = [
            node
            for node in expected
            if nodes[node]["name"] == root[0]
            and nodes[node]["content_sha256"] == root[1]
        ]
        if len(root_matches) != 1:
            raise ValueError(f"root context identity is ambiguous for {root[0]}")
        root_node = root_matches[0]
        distances = {root_node: 0}
        pending = deque([root_node])
        while pending:
            current = pending.popleft()
            for child in sorted(adjacency[current]):
                if child not in distances:
                    distances[child] = distances[current] + 1
                    pending.append(child)
        if set(distances) != expected:
            raise ValueError(f"reachability replay differs for {root[0]}")
        for node, distance in distances.items():
            root_distances[node][root] = distance

    rows = []
    for node in sorted(nodes):
        reached_by = root_distances[node]
        affected_facts = sorted(
            {
                fact
                for root in reached_by
                for fact in roots[root]["affected_fact_ids"]
            }
        )
        rendered_roots = sorted(root[0] for root in reached_by)
        distances = list(reached_by.values())
        descriptor = nodes[node]
        namespace = descriptor["name"].split(".", 1)[0]
        focus_eligible = (
            namespace in {"Nat", "Int", "List"}
            and min(distances) <= 4
            and (len(reached_by) >= 2 or len(affected_facts) >= 3)
        )
        rows.append(
            {
                "source_node_id": node,
                "context_sha256": descriptor["context_sha256"],
                "name": descriptor["name"],
                "content_sha256": descriptor["content_sha256"],
                "dependency_sha256": descriptor["dependency_sha256"],
                "is_semantic_contract_root": any(
                    descriptor["name"] == root[0]
                    and descriptor["content_sha256"] == root[1]
                    for root in roots
                ),
                "reached_by_source_names": rendered_roots,
                "reached_by_source_identities": len(reached_by),
                "affected_fact_ids": affected_facts,
                "affected_targets": len(affected_facts),
                "minimum_transparent_depth": min(distances),
                "maximum_transparent_depth": max(distances),
                "direct_transparent_consumers": sorted(
                    {nodes[consumer]["name"] for consumer in reverse[node]}
                ),
                "direct_transparent_consumer_identities": len(reverse[node]),
                "contract_focus_eligible": focus_eligible,
            }
        )
    focus = [row for row in rows if row["contract_focus_eligible"]]
    focus.sort(
        key=lambda row: (
            -row["affected_targets"],
            -row["reached_by_source_identities"],
            row["minimum_transparent_depth"],
            -row["direct_transparent_consumer_identities"],
            row["name"],
            row["content_sha256"],
        )
    )
    for rank, row in enumerate(focus, 1):
        row["contract_focus_rank"] = rank
    rows.sort(key=lambda row: (row["name"], row["content_sha256"]))
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-imported-implementation-frontier",
        "state": "reverse-reachability-strategy-projection",
        "authority": "strategy context only; reachability and rank grant no semantic contract, proof, operation, applicability, transport, or fact-transition authority",
        "source": {
            "implementation_graph_path": str(GRAPH.relative_to(ROOT)),
            "implementation_graph_sha256": digest(GRAPH),
            "semantic_contract_demand_path": str(DEMAND.relative_to(ROOT)),
            "semantic_contract_demand_sha256": digest(DEMAND),
        },
        "census": {
            "transparent_structural_identities": len(rows),
            "semantic_contract_roots": len(roots),
            "contract_focus_eligible_identities": len(focus),
        },
        "focus_ranking": focus,
        "nodes": rows,
        "limitations": "Ranking is deterministic scheduling context over checked reachability. It does not establish that unfolding, transporting, or contracting any node is useful or sound.",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    rendered = json.dumps(
        build(json.loads(GRAPH.read_text()), json.loads(DEMAND.read_text())),
        indent=2,
        sort_keys=True,
    ) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            print("IMPORTED_IMPLEMENTATION_FRONTIER_ERROR|artifact is stale")
            return 1
    else:
        args.output.write_text(rendered)
    census = json.loads(rendered)["census"]
    print(
        "IMPORTED_IMPLEMENTATION_FRONTIER|"
        f"nodes={census['transparent_structural_identities']}|"
        f"roots={census['semantic_contract_roots']}|"
        f"focus={census['contract_focus_eligible_identities']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
