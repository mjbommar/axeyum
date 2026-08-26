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
        raise ValueError("root inventory is absent")
    observed = {(row.get("source_name"), row.get("source_content_sha256")) for row in roots}
    if observed != expected:
        raise ValueError("root identities do not exactly match semantic-contract demand")

    global_nodes = data.get("transparent_nodes")
    global_edges = data.get("edges")
    if not isinstance(global_nodes, list) or not isinstance(global_edges, list):
        raise ValueError("global graph inventory is absent")
    node_keys = [(node.get("name"), node.get("content_sha256")) for node in global_nodes]
    if node_keys != sorted(node_keys) or len(node_keys) != len(set(node_keys)):
        raise ValueError("global transparent node order or identity is unstable")
    edge_keys = [
        (
            edge.get("from"),
            edge.get("from_content_sha256"),
            edge.get("to"),
            edge.get("to_content_sha256"),
            edge.get("to_kind"),
        )
        for edge in global_edges
    ]
    if edge_keys != sorted(edge_keys) or len(edge_keys) != len(set(edge_keys)):
        raise ValueError("global edge order or identity is unstable")
    node_key_set = set(node_keys)
    if any((source, source_hash) not in node_key_set for source, source_hash, _target, _target_hash, _kind in edge_keys):
        raise ValueError("global edge starts outside the transparent graph")
    if any(kind == "definition" and (target, target_hash) not in node_key_set for _source, _source_hash, target, target_hash, kind in edge_keys):
        raise ValueError("global graph omits a reachable transparent definition")

    node_occurrences = 0
    edge_occurrences = 0
    for row in roots:
        names = row.get("reachable_transparent_nodes")
        if not isinstance(names, list):
            raise ValueError(f"{row.get('source_name')} reachability is malformed")
        names = [(node.get("name"), node.get("content_sha256")) for node in names]
        if names != sorted(names) or len(names) != len(set(names)):
            raise ValueError(f"{row.get('source_name')} node order is unstable")
        if (row.get("source_name"), row.get("source_content_sha256")) not in names:
            raise ValueError(f"{row.get('source_name')} root is absent from its graph")
        if not set(names).issubset(node_key_set):
            raise ValueError(f"{row.get('source_name')} reaches an absent global node")
        node_occurrences += len(names)
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
    observed_named_edges = {(source, target, kind) for source, _source_hash, target, _target_hash, kind in edge_keys}
    if not required_modulus_edges.issubset(observed_named_edges):
        raise ValueError("imported Nat.mod decision/subtraction spine is incomplete")
    census = data.get("census", {})
    actual = {
        "root_definition_identities": len(roots),
        "transparent_node_occurrences": node_occurrences,
        "direct_edge_occurrences": edge_occurrences,
        "distinct_transparent_nodes": len(global_nodes),
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
    if actual["distinct_transparent_nodes"] != 366 or actual["distinct_direct_edges"] != 2219:
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
