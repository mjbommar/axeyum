#!/usr/bin/env python3
"""Rank proof-isolated kernel lemmas for visible open nursery goals.

This is deliberately retrieval, not proving.  It reads only train/development
fact statements plus the generated kernel lemma index.  Held-out facts are
excluded before tokenization.  Scores are deterministic lexical/type-vocabulary
overlap and grant no applicability, proof, operation, or admission authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
LEMMA_INDEX = ROOT / "artifacts/autogenesis/kernel-lemma-search-index-v1.json"
OUTPUT = ROOT / "artifacts/autogenesis/open-lemma-candidate-ranking-v1.json"
MAX_CANDIDATES = 12

STOP = {
    "a",
    "an",
    "and",
    "ax",
    "eq",
    "false",
    "for",
    "forall",
    "fun",
    "if",
    "in",
    "is",
    "let",
    "of",
    "or",
    "prop",
    "sort",
    "the",
    "then",
    "true",
    "x",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def split_identifier(value: str) -> list[str]:
    value = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", value)
    return re.findall(r"[A-Za-z][A-Za-z0-9]*", value.replace("_", " "))


def tokens(value: str) -> set[str]:
    value = (
        value.replace("ℕ", " Nat ")
        .replace("ℤ", " Int ")
        .replace("≡", " ModEq ")
        .replace("%", " Mod ")
        .replace("+", " Add ")
        .replace("*", " Mul ")
        .replace("∣", " Dvd ")
        .replace("≤", " Le ")
        .replace("≥", " Ge ")
        .replace("<", " Lt ")
        .replace(">", " Gt ")
    )
    result = set()
    for raw in split_identifier(value):
        token = raw.lower()
        token = {"axnat": "nat", "axint": "int"}.get(token, token)
        if token not in STOP and len(token) > 1 and not re.fullmatch(r"x\d+", token):
            result.add(token)
    return result


def eligible_facts(
    facts: dict[str, dict[str, Any]], nursery: dict[str, Any]
) -> tuple[list[dict[str, Any]], list[str]]:
    partitions = {
        row["fact_id"]: row["partition"]
        for row in nursery.get("entries", [])
        if isinstance(row, dict)
        and isinstance(row.get("fact_id"), str)
        and isinstance(row.get("partition"), str)
    }
    eligible = []
    excluded_held_out = []
    for fact_id, partition in sorted(partitions.items()):
        if partition == "held-out":
            excluded_held_out.append(fact_id)
            continue
        if partition not in {"train", "development"}:
            continue
        fact = facts.get(fact_id)
        if fact is None:
            raise ValueError(f"nursery fact is absent from ledger: {fact_id}")
        formal = fact.get("formal", {})
        if (
            fact.get("epistemic_status") in {"open", "conjectured"}
            and str(formal.get("language", "")).startswith("lean4")
            and isinstance(formal.get("statement"), str)
            and formal["statement"].strip()
        ):
            eligible.append(fact)
    return eligible, excluded_held_out


def rank(fact: dict[str, Any], lemmas: list[dict[str, Any]]) -> list[dict[str, Any]]:
    statement_tokens = tokens(fact["formal"]["statement"])
    fragment_tokens = tokens(str(fact["formal"].get("fragment", "")))
    rows = []
    for lemma in lemmas:
        name_tokens = tokens(lemma["kernel_declaration_id"])
        dependency_tokens = tokens(" ".join(lemma["direct_type_dependencies"]))
        type_tokens = tokens(lemma["canonical_type"])
        name_overlap = sorted(statement_tokens & name_tokens)
        dependency_overlap = sorted(statement_tokens & dependency_tokens)
        type_overlap = sorted(statement_tokens & type_tokens)
        fragment_overlap = sorted(
            fragment_tokens & (name_tokens | dependency_tokens | type_tokens)
        )
        score = (
            6 * len(name_overlap)
            + 3 * len(dependency_overlap)
            + len(type_overlap)
            + 2 * len(fragment_overlap)
        )
        if score == 0:
            continue
        rows.append(
            {
                "kernel_declaration_id": lemma["kernel_declaration_id"],
                "score": score,
                "name_token_overlap": name_overlap,
                "type_dependency_token_overlap": dependency_overlap,
                "canonical_type_token_overlap": type_overlap,
                "fragment_token_overlap": fragment_overlap,
                "direct_reverse_theorem_reference_count": len(
                    lemma["direct_theorem_dependents"]
                ),
                "axiom_footprint_size": lemma["axiom_footprint_size"],
                "exact_fact_ids": lemma["exact_fact_ids"],
            }
        )
    rows.sort(
        key=lambda row: (
            -row["score"],
            -row["direct_reverse_theorem_reference_count"],
            row["kernel_declaration_id"],
        )
    )
    return rows[:MAX_CANDIDATES]


def build() -> dict[str, Any]:
    facts = {
        fact["id"]: fact
        for path in sorted(FACTS.glob("F-*.json"))
        for fact in [json.loads(path.read_text())]
    }
    nursery = json.loads(NURSERY.read_text())
    index = json.loads(LEMMA_INDEX.read_text())
    population, excluded_held_out = eligible_facts(facts, nursery)
    goals = []
    for fact in population:
        candidates = rank(fact, index["lemmas"])
        goals.append(
            {
                "fact_id": fact["id"],
                "partition": next(
                    row["partition"]
                    for row in nursery["entries"]
                    if row["fact_id"] == fact["id"]
                ),
                "formal_fragment": fact["formal"].get("fragment"),
                "statement_tokens": sorted(tokens(fact["formal"]["statement"])),
                "mutation_of": next(
                    (
                        row.get("mutation_of")
                        for row in nursery["entries"]
                        if row["fact_id"] == fact["id"]
                    ),
                    None,
                ),
                "candidate_count": len(candidates),
                "candidates": candidates,
            }
        )
    goals.sort(key=lambda row: row["fact_id"])
    return {
        "schema_version": 1,
        "kind": "axeyum-open-lemma-candidate-ranking",
        "state": "candidate-only-train-development-held-out-unread",
        "derivation": {
            "nursery_sha256": digest(NURSERY),
            "lemma_index_sha256": digest(LEMMA_INDEX),
            "population_rule": "open or conjectured lean4 fact in train or development",
            "ranking_rule": "weighted exact token overlap over visible statement, kernel declaration name, canonical type, direct type dependencies, and formal fragment; deterministic graph-centrality tie break",
            "max_candidates_per_goal": MAX_CANDIDATES,
            "forbidden_inputs": [
                "held-out fact statement or outcome",
                "source theorem proof body",
                "target kernel theorem proof value",
                "direct_declaration_dependencies or direct_theorem_dependencies as target evidence",
                "producer outcome",
            ],
            "trust_boundary": "untrusted retrieval context only; never applicability, proof, operation, fact status, or admission authority",
        },
        "census": {
            "eligible_goals": len(goals),
            "goals_with_candidates": sum(bool(row["candidates"]) for row in goals),
            "candidate_rows": sum(len(row["candidates"]) for row in goals),
            "held_out_fact_ids_excluded_before_tokenization": len(excluded_held_out),
        },
        "excluded_held_out_fact_ids": excluded_held_out,
        "goals": goals,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text() != rendered:
            print("OPEN_LEMMA_CANDIDATE_RANKING_ERROR|artifact is stale")
            return 1
    else:
        OUTPUT.write_text(rendered)
    census = json.loads(rendered)["census"]
    print(
        "OPEN_LEMMA_CANDIDATE_RANKING|"
        f"goals={census['eligible_goals']}|"
        f"with_candidates={census['goals_with_candidates']}|"
        f"rows={census['candidate_rows']}|"
        f"held_out_excluded={census['held_out_fact_ids_excluded_before_tokenization']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
