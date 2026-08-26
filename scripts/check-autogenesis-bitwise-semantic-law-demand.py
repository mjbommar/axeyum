#!/usr/bin/env python3
"""Check the exact semantic-law demand for Nat.testBit_bitwise."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "artifacts/autogenesis/bitwise-semantic-law-demand-v1.json"
CANDIDATE = ROOT / "artifacts/autogenesis/imported-testbit-bitwise-candidate-v1.json"
GRAPH = ROOT / "artifacts/autogenesis/imported-implementation-demand-v1.json"


def validate(data: dict[str, Any]) -> dict[str, int]:
    if data.get("kind") != "axeyum-autogenesis-semantic-law-demand":
        raise ValueError("wrong artifact kind")
    if data.get("state") != "law-interface-required-before-reconstruction":
        raise ValueError("semantic-law demand state changed")
    authority = data.get("authority", "")
    for denied in ("no proof authority", "no transport", "no fact-transition"):
        if denied not in authority:
            raise ValueError(f"authority does not deny {denied}")

    candidate = json.loads(CANDIDATE.read_text())
    expected = candidate["candidate"]
    subject = data.get("candidate", {})
    if subject.get("name") != expected.get("name"):
        raise ValueError("candidate name drifted")
    if subject.get("alpha_type_expression_sha256") != expected.get(
        "alpha_type_expression_sha256"
    ):
        raise ValueError("candidate type identity drifted")

    graph = json.loads(GRAPH.read_text())
    graph_identities = {
        (node.get("name"), node.get("content_sha256")) for node in graph["nodes"]
    }
    operations = data.get("operations")
    if not isinstance(operations, list) or len(operations) != 2:
        raise ValueError("operation identity population changed")
    for operation in operations:
        if (operation.get("name"), operation.get("content_sha256")) not in graph_identities:
            raise ValueError("operation identity is absent from implementation graph")

    laws = data.get("laws")
    if not isinstance(laws, list) or len(laws) != 6:
        raise ValueError("semantic-law population changed")
    names = [law.get("name") for law in laws]
    if names != [
        "testBit_zero_value",
        "testBit_low",
        "testBit_succ",
        "boolean_numeric_observation_transport",
        "bitwise_equation",
        "double_add_div",
    ]:
        raise ValueError("semantic-law order or identity changed")
    imported_dependencies = set(expected["direct_theorem_dependencies"])
    for law in laws:
        if (
            law.get("availability") == "imported-candidate-dependency-assumption-bearing"
            and law.get("source_declaration") not in imported_dependencies
        ):
            raise ValueError("claimed imported law is absent from direct dependencies")

    index = json.loads(
        (ROOT / "artifacts/autogenesis/kernel-lemma-search-index-v1.json").read_text()
    )
    indexed = {row["kernel_declaration_id"]: row for row in index["lemmas"]}
    analogues = data.get("native_analogues")
    if not isinstance(analogues, list) or len(analogues) != 2:
        raise ValueError("native analogue population changed")
    for analogue in analogues:
        declaration_id = analogue.get("kernel_declaration_id")
        live = indexed.get(declaration_id)
        if live is None or live.get("axiom_footprint_size") != 0:
            raise ValueError("native analogue is absent or assumption-bearing")
        if analogue.get("canonical_type") != live.get("canonical_type"):
            raise ValueError("native analogue type identity drifted")
        if "Eq.{1} AxNat" not in analogue["canonical_type"]:
            raise ValueError("native analogue no longer exposes the numeric result sort")
    transport = laws[3]
    if transport.get("availability") != "missing-typed-transport":
        raise ValueError("Boolean/numeric observation transport status changed")

    exclusion = data.get("countermodel_exclusion", {})
    if exclusion.get("excluded_by_law") != "testBit_succ":
        raise ValueError("countermodel exclusion law changed")
    test_bit = lambda n, _i: n == 1
    n, i = exclusion.get("n"), exclusion.get("i")
    if (n, i) != (2, 0):
        raise ValueError("countermodel exclusion witness changed")
    lhs = test_bit(n, i + 1)
    rhs = test_bit(n // 2, i)
    if lhs == rhs:
        raise ValueError("semantic law no longer excludes the countermodel")
    if (exclusion.get("law_lhs"), exclusion.get("law_rhs")) != (lhs, rhs):
        raise ValueError("countermodel exclusion receipt changed")
    return {
        "laws": len(laws),
        "native_analogues": len(analogues),
        "operations": len(operations),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path, default=ARTIFACT)
    args = parser.parse_args()
    try:
        result = validate(json.loads(args.artifact.read_text()))
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as error:
        print(f"BITWISE_SEMANTIC_LAW_DEMAND_ERROR|{error}")
        return 1
    print(
        "BITWISE_SEMANTIC_LAW_DEMAND_OK|"
        f"laws={result['laws']}|operations={result['operations']}|"
        f"native_analogues={result['native_analogues']}|"
        "countermodel_excluded=true|reconstruction_eligible=false"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
