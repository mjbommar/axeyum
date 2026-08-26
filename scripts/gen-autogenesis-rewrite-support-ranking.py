#!/usr/bin/env python3
"""Add graph-derived connective lemmas to a proof-isolated goal ranking.

The first-stage ranking finds lemmas whose names and types resemble a visible
goal.  A proof often needs a second kind of premise: a generic equation about
an operator introduced by one of those topical lemmas.  This projection ranks
that connective layer from the selected lemmas' canonical types.  It reads no
target proof, producer outcome, held-out statement, or per-target override.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PRIMARY = ROOT / "artifacts/autogenesis/open-lemma-candidate-ranking-v1.json"
INDEX = ROOT / "artifacts/autogenesis/kernel-lemma-search-index-v1.json"
OUTPUT = ROOT / "artifacts/autogenesis/open-lemma-rewrite-support-ranking-v1.json"
ANCHOR_COUNT = 4
SUPPORT_COUNT = 8

GENERIC = {
    "axnat",
    "axint",
    "eq",
    "false",
    "int",
    "nat",
    "prop",
    "sort",
    "true",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tokens(value: str) -> set[str]:
    value = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", value.replace("_", " "))
    return {
        token.lower()
        for token in re.findall(r"[A-Za-z][A-Za-z0-9]*", value)
        if len(token) > 1 and token.lower() not in GENERIC
    }


def support_rows(
    goal: dict[str, Any], lemma_by_name: dict[str, dict[str, Any]]
) -> list[dict[str, Any]]:
    primary = goal["candidates"]
    primary_names = {row["kernel_declaration_id"] for row in primary}
    statement_tokens = set(goal["statement_tokens"]) | GENERIC
    bridge_tokens: set[str] = set()
    anchors = primary[:ANCHOR_COUNT]
    for row in anchors:
        lemma = lemma_by_name[row["kernel_declaration_id"]]
        bridge_tokens |= tokens(lemma["canonical_type"])
        bridge_tokens |= tokens(" ".join(lemma["direct_type_dependencies"]))
    bridge_tokens -= statement_tokens
    anchor_namespaces = {
        row["kernel_declaration_id"].partition(".")[0] for row in anchors
    }

    rows = []
    for name, lemma in lemma_by_name.items():
        if (
            name in primary_names
            or lemma["axiom_footprint_size"] != 0
            or name.partition(".")[0] not in anchor_namespaces
            or "Eq." not in lemma["canonical_type"]
        ):
            continue
        name_overlap = sorted(bridge_tokens & tokens(name))
        dependency_overlap = sorted(
            bridge_tokens & tokens(" ".join(lemma["direct_type_dependencies"]))
        )
        type_overlap = sorted(bridge_tokens & tokens(lemma["canonical_type"]))
        # A support lemma must advertise the bridge operator in its own name.
        # Type-only overlap would make almost every theorem in a family tie.
        if not name_overlap:
            continue
        score = 6 * len(name_overlap) + 2 * len(dependency_overlap) + len(type_overlap)
        rows.append(
            {
                "kernel_declaration_id": name,
                "score": score,
                "retrieval_role": "rewrite-support",
                "bridge_token_overlap": name_overlap,
                "type_dependency_bridge_overlap": dependency_overlap,
                "canonical_type_bridge_overlap": type_overlap,
                "direct_type_dependency_count": len(
                    lemma["direct_type_dependencies"]
                ),
                "direct_reverse_theorem_reference_count": len(
                    lemma["direct_theorem_dependents"]
                ),
                "axiom_footprint_size": 0,
                "exact_fact_ids": lemma["exact_fact_ids"],
            }
        )
    rows.sort(
        key=lambda row: (
            -len(row["bridge_token_overlap"]),
            row["direct_type_dependency_count"],
            -row["score"],
            -row["direct_reverse_theorem_reference_count"],
            row["kernel_declaration_id"],
        )
    )
    return rows[:SUPPORT_COUNT]


def build(primary: dict[str, Any], index: dict[str, Any]) -> dict[str, Any]:
    lemma_by_name = {
        row["kernel_declaration_id"]: row for row in index["lemmas"]
    }
    goals = []
    for source in primary["goals"]:
        support = support_rows(source, lemma_by_name)
        anchors = source["candidates"][:ANCHOR_COUNT]
        remainder = source["candidates"][ANCHOR_COUNT:]
        candidates = [
            {**row, "retrieval_role": row.get("retrieval_role", "goal-primary")}
            for row in [*anchors, *support, *remainder]
        ]
        goals.append(
            {
                **source,
                "candidate_count": len(candidates),
                "primary_candidate_count": len(source["candidates"]),
                "rewrite_support_candidate_count": len(support),
                "candidates": candidates,
            }
        )
    return {
        "schema_version": 1,
        "kind": "axeyum-open-lemma-rewrite-support-ranking",
        "state": primary["state"],
        "derivation": {
            "primary_ranking_path": str(PRIMARY.relative_to(ROOT)),
            "primary_ranking_sha256": digest(PRIMARY),
            "lemma_index_path": str(INDEX.relative_to(ROOT)),
            "lemma_index_sha256": digest(INDEX),
            "anchor_count": ANCHOR_COUNT,
            "max_support_candidates_per_goal": SUPPORT_COUNT,
            "support_rule": "rank axiom-free lemmas whose names contain non-goal type vocabulary introduced by first-stage candidates; stable score, graph-centrality, and declaration-name ordering",
            "forbidden_inputs": [
                "held-out fact statement or outcome",
                "source theorem proof body",
                "target kernel theorem proof value",
                "producer outcome",
                "per-target candidate override",
            ],
            "trust_boundary": "untrusted retrieval context only; kernel admission remains authority",
        },
        "census": {
            "eligible_goals": len(goals),
            "primary_candidate_rows": sum(
                row["primary_candidate_count"] for row in goals
            ),
            "rewrite_support_candidate_rows": sum(
                row["rewrite_support_candidate_count"] for row in goals
            ),
            "combined_candidate_rows": sum(row["candidate_count"] for row in goals),
        },
        "excluded_held_out_fact_ids": primary["excluded_held_out_fact_ids"],
        "goals": goals,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--primary", type=Path, default=PRIMARY)
    parser.add_argument("--index", type=Path, default=INDEX)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    result = build(
        json.loads(args.primary.read_text()), json.loads(args.index.read_text())
    )
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            print("REWRITE_SUPPORT_RANKING_ERROR|artifact is stale")
            return 1
    else:
        args.output.write_text(rendered)
    census = result["census"]
    print(
        "REWRITE_SUPPORT_RANKING|"
        f"goals={census['eligible_goals']}|"
        f"primary={census['primary_candidate_rows']}|"
        f"support={census['rewrite_support_candidate_rows']}|"
        f"combined={census['combined_candidate_rows']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
