#!/usr/bin/env python3
"""Fail-closed checks for the imported implementation-demand graph."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "artifacts/autogenesis/imported-implementation-demand-v1.json"
REPLAY = ROOT / "artifacts/autogenesis/retrieved-induction-type-slice-replay-v1.json"
SEMANTIC_DEMAND = ROOT / "artifacts/autogenesis/semantic-contract-demand-v1.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(data: dict[str, Any], replay: dict[str, Any], demand: dict[str, Any]) -> dict[str, int]:
    if data.get("kind") != "axeyum-autogenesis-imported-implementation-demand":
        raise ValueError("wrong artifact kind")
    if data.get("state") != "proof-isolated-strategy-graph":
        raise ValueError("artifact is not proof-isolated strategy data")
    authority = data.get("authority", "")
    if "no theorem proof" not in authority or "semantic contract" not in authority:
        raise ValueError("authority boundary is missing")
    if data.get("source", {}).get("type_slice_replay_sha256") != digest(REPLAY):
        raise ValueError("type-slice replay identity is stale")
    if replay.get("authority", {}).get("proof_bodies_requested") is not False:
        raise ValueError("source replay exposed proof bodies")
    if replay.get("authority", {}).get("held_out_inspected") is not False:
        raise ValueError("source replay inspected held-out targets")

    expected = {
        (row["source_name"], row["source_content_sha256"])
        for row in demand["demands"]
    }
    roots = data.get("roots")
    if not isinstance(roots, list):
        raise TypeError("root inventory is absent")
    observed = {(row.get("source_name"), row.get("source_content_sha256")) for row in roots}
    if observed != expected:
        raise ValueError("root identities do not exactly match semantic-contract demand")

    global_nodes = data.get("nodes")
    global_edges = data.get("edges")
    if not isinstance(global_nodes, list) or not isinstance(global_edges, list):
        raise TypeError("global graph inventory is absent")
    node_ids = [node.get("node_id") for node in global_nodes]
    if node_ids != list(range(len(global_nodes))):
        raise ValueError("global node IDs are not dense and stable")
    node_keys = [
        (node.get("context_sha256"), node.get("name"), node.get("content_sha256"), node.get("dependency_sha256"))
        for node in global_nodes
    ]
    if node_keys != sorted(node_keys) or len(node_keys) != len(set(node_keys)):
        raise ValueError("global node order or identity is unstable")
    edge_keys = [(edge.get("from_node_id"), edge.get("to_node_id")) for edge in global_edges]
    if edge_keys != sorted(edge_keys) or len(edge_keys) != len(set(edge_keys)):
        raise ValueError("global edge order or identity is unstable")
    if any(source not in node_ids or target not in node_ids for source, target in edge_keys):
        raise ValueError("global edge endpoint is absent")
    nodes_by_id = {node["node_id"]: node for node in global_nodes}
    if any(nodes_by_id[source]["kind"] != "definition" for source, _target in edge_keys):
        raise ValueError("global edge starts outside the transparent graph")

    node_occurrences = 0
    edge_occurrences = 0
    for row in roots:
        ids = row.get("reachable_transparent_node_ids")
        if not isinstance(ids, list):
            raise TypeError(f"{row.get('source_name')} reachability is malformed")
        if ids != sorted(ids) or len(ids) != len(set(ids)):
            raise ValueError(f"{row.get('source_name')} node order is unstable")
        if not any(
            nodes_by_id[node_id]["name"] == row.get("source_name")
            and nodes_by_id[node_id]["content_sha256"] == row.get("source_content_sha256")
            for node_id in ids
        ):
            raise ValueError(f"{row.get('source_name')} root is absent from its graph")
        if any(node_id not in nodes_by_id for node_id in ids):
            raise ValueError(f"{row.get('source_name')} reaches an absent global node")
        if any(nodes_by_id[node_id]["kind"] != "definition" for node_id in ids):
            raise ValueError(f"{row.get('source_name')} reaches a nontransparent node")
        node_occurrences += len(ids)
        edge_occurrences += row.get("direct_edge_occurrences", 0)

    required_modulus_edges = {
        ("Nat.mod", "Nat.modCore", "definition"),
        ("Nat.mod", "Nat.decLe", "definition"),
        ("Nat.decLe", "Nat.ble", "definition"),
        ("Nat.modCore", "Nat.decLt", "definition"),
        ("Nat.modCore", "Nat.modCore.go", "definition"),
        ("Nat.modCore.go", "Nat.modCore.go._f", "definition"),
        ("Nat.modCore.go._f", "instSubNat", "definition"),
    }
    observed_named_edges = {
        (nodes_by_id[source]["name"], nodes_by_id[target]["name"], nodes_by_id[target]["kind"])
        for source, target in edge_keys
    }
    if not required_modulus_edges.issubset(observed_named_edges):
        raise ValueError("imported Nat.mod decision/subtraction spine is incomplete")
    census = data.get("census", {})
    actual = {
        "root_definition_identities": len(roots),
        "transparent_node_occurrences": node_occurrences,
        "direct_edge_occurrences": edge_occurrences,
        "distinct_declaration_nodes": len(global_nodes),
        "distinct_transparent_nodes": sum(node["kind"] == "definition" for node in global_nodes),
        "distinct_direct_edges": len(global_edges),
    }
    if census != actual:
        raise ValueError(f"census mismatch: expected {actual}, found {census}")
    reviewed_occurrences = {
        "root_definition_identities": 14,
        "transparent_node_occurrences": 1363,
        "direct_edge_occurrences": 7303,
    }
    if {key: actual[key] for key in reviewed_occurrences} != reviewed_occurrences:
        raise ValueError(f"reviewed implementation population changed: {actual}")
    if (
        actual["distinct_declaration_nodes"] != 1734
        or actual["distinct_transparent_nodes"] != 1000
        or actual["distinct_direct_edges"] != 5421
    ):
        raise ValueError(f"reviewed deduplicated graph changed: {actual}")
    return actual


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path, default=ARTIFACT)
    args = parser.parse_args()
    try:
        census = validate(
            json.loads(args.artifact.read_text()),
            json.loads(REPLAY.read_text()),
            json.loads(SEMANTIC_DEMAND.read_text()),
        )
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        print(f"IMPORTED_IMPLEMENTATION_DEMAND_ERROR|{error}")
        return 1
    print(
        "IMPORTED_IMPLEMENTATION_DEMAND_OK|"
        f"roots={census['root_definition_identities']}|"
        f"transparent_nodes={census['transparent_node_occurrences']}|"
        f"edges={census['direct_edge_occurrences']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
