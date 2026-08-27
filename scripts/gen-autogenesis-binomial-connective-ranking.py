#!/usr/bin/env python3
"""Project a compact proof-dependency spine for the measured arrow goals.

This is additive: it leaves the population-wide ranking and its historical
measurements byte-for-byte unchanged.  The projection reads only visible
train/development identities, the existing held-out-safe ranking, and the
constructed kernel's checked theorem-dependency graph.  It never reads a
target proof or producer outcome.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
from collections import Counter
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "artifacts/autogenesis/open-lemma-rewrite-support-ranking-v1.json"
INDEX = ROOT / "artifacts/autogenesis/kernel-lemma-search-index-v1.json"
CAPABILITY = ROOT / "artifacts/autogenesis/binomial-arrow-export-capability-v1.json"
OUTPUT = ROOT / "artifacts/autogenesis/binomial-arrow-connective-ranking-v1.json"
MAX_CANDIDATES = 3

GENERIC = {"axint", "axnat", "eq", "int", "ml430", "nat", "of", "prop", "sort"}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tokens(value: str) -> set[str]:
    value = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", value.replace("_", " ").replace("-", " "))
    return {
        token.lower()
        for token in re.findall(r"[A-Za-z][A-Za-z0-9]*", value)
        if len(token) > 1 and token.lower() not in GENERIC
    }


def build(base: dict[str, Any], index: dict[str, Any], capability: dict[str, Any]) -> dict[str, Any]:
    lemma_by_name = {row["kernel_declaration_id"]: row for row in index["lemmas"]}
    document_frequency = Counter(
        token for name in lemma_by_name for token in tokens(name)
    )
    population = {row["fact_id"] for row in capability["rows"]}
    base_goals = {row["fact_id"]: row for row in base["goals"]}
    missing = sorted(population - set(base_goals))
    if missing:
        raise ValueError(f"capability facts absent from base ranking: {missing}")

    def identity_score(name: str, query: set[str]) -> float:
        name_overlap = query & tokens(name)
        weighted = sum(
            math.log((len(lemma_by_name) + 1) / (document_frequency[token] + 1)) + 1
            for token in name_overlap
        )
        type_overlap = query & tokens(lemma_by_name[name]["canonical_type"])
        return 10 * weighted + len(type_overlap)

    goals = []
    for fact_id in sorted(population):
        source = base_goals[fact_id]
        query = set(source["statement_tokens"]) | tokens(fact_id)
        base_names = [row["kernel_declaration_id"] for row in source["candidates"]]
        seed_pool = {
            dependency
            for name in base_names
            for dependency in lemma_by_name[name]["direct_theorem_dependencies"]
            if dependency in lemma_by_name
            and lemma_by_name[dependency]["axiom_footprint_size"] == 0
        }
        seed = min(seed_pool, key=lambda name: (-identity_score(name, query), name))
        selected: list[tuple[str, int, str | None, float]] = [
            (seed, 1, None, identity_score(seed, query))
        ]
        seed_tokens = tokens(lemma_by_name[seed]["canonical_type"])
        bridge_tokens = seed_tokens - query
        simplifiers = []
        for name in lemma_by_name[seed]["direct_theorem_dependencies"]:
            lemma = lemma_by_name.get(name)
            if (
                lemma is None
                or lemma["axiom_footprint_size"] != 0
                or "Eq." not in lemma["canonical_type"]
            ):
                continue
            score = (
                identity_score(name, query)
                + 100 * len(bridge_tokens & tokens(name))
                + 10 * len(bridge_tokens & tokens(lemma["canonical_type"]))
            )
            simplifiers.append((name, score))
        simplifiers.sort(key=lambda row: (-row[1], row[0]))
        if simplifiers:
            simplifier, score = simplifiers[0]
            selected.append((simplifier, 2, seed, score))
            premise_producers = []
            for name in lemma_by_name[simplifier]["direct_theorem_dependencies"]:
                lemma = lemma_by_name.get(name)
                if (
                    lemma is None
                    or lemma["axiom_footprint_size"] != 0
                    or "Eq." in lemma["canonical_type"]
                ):
                    continue
                score = (
                    identity_score(name, query)
                    + 10
                    * len(
                        bridge_tokens
                        & (tokens(name) | tokens(lemma["canonical_type"]))
                    )
                )
                premise_producers.append((name, score))
            premise_producers.sort(key=lambda row: (-row[1], row[0]))
            if premise_producers:
                premise, score = premise_producers[0]
                selected.append((premise, 3, simplifier, score))

        rows = []
        for name, depth, parent, score in selected:
            lemma = lemma_by_name[name]
            rows.append(
                {
                    "kernel_declaration_id": name,
                    "retrieval_role": "dependency-spine",
                    "dependency_depth": depth,
                    "dependency_parent": parent,
                    "score": round(score, 6),
                    "query_name_token_overlap": sorted(query & tokens(name)),
                    "axiom_footprint_size": 0,
                    "exact_fact_ids": lemma["exact_fact_ids"],
                }
            )
        rows = rows[:MAX_CANDIDATES]
        goals.append(
            {
                **source,
                "candidates": rows,
                "candidate_count": len(rows),
                "connective_seed": seed,
                "dependency_spine_count": sum(
                    row["retrieval_role"] == "dependency-spine" for row in rows
                ),
            }
        )

    return {
        "schema_version": 1,
        "kind": "axeyum-binomial-arrow-connective-ranking",
        "state": "train-development-projection-held-out-excluded",
        "authority": "retrieval hints only; proof construction and kernel admission remain independent",
        "source": {
            "base_ranking": str(BASE.relative_to(ROOT)),
            "base_ranking_sha256": digest(BASE),
            "kernel_lemma_search_index": str(INDEX.relative_to(ROOT)),
            "kernel_lemma_search_index_sha256": digest(INDEX),
            "binomial_arrow_capability": str(CAPABILITY.relative_to(ROOT)),
            "binomial_arrow_capability_sha256": digest(CAPABILITY),
            "max_candidates_per_goal": MAX_CANDIDATES,
            "max_dependency_depth": 3,
            "selection_rule": "IDF-weighted visible identity seed, one equality simplifier for seed-introduced vocabulary, then one non-equality premise producer from the checked dependency graph",
            "forbidden_inputs": [
                "target theorem proof",
                "producer outcome or decline trace",
                "per-target candidate override",
                "held-out identity or statement",
            ],
        },
        "held_out_exclusion": base["held_out_exclusion"],
        "goals": goals,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = build(json.loads(BASE.read_text()), json.loads(INDEX.read_text()), json.loads(CAPABILITY.read_text()))
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text() != rendered:
            print("BINOMIAL_CONNECTIVE_RANKING_ERROR|generated artifact is stale")
            return 1
    else:
        OUTPUT.write_text(rendered)
    print(
        f"BINOMIAL_CONNECTIVE_RANKING|goals={len(result['goals'])}|"
        f"candidates={sum(len(row['candidates']) for row in result['goals'])}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
