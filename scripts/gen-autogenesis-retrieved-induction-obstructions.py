#!/usr/bin/env python3
"""Project retrieved-induction outcomes into typed capability demand."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
AUTO = ROOT / "artifacts/autogenesis"
CENSUS = AUTO / "open-ranked-transport-induction-census-v1.json"
RANKING = AUTO / "open-lemma-rewrite-support-ranking-v1.json"
OUTPUT = AUTO / "retrieved-induction-obstruction-projection-v1.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def classify(row: dict[str, Any]) -> tuple[str, str]:
    result = row["result"]
    if result == "accepted":
        return "checked-proof", "authoritative-operation-integration"
    if result == "import_rejected":
        return "statement-boundary", "type-slice-generalization"
    reason = row.get("reason_kind")
    if reason == "NotEqualityGoal":
        return "producer-grammar", "non-equality-terminal-family"
    if reason == "BinderBudgetExceeded":
        return "producer-grammar", "binder-or-generalization"
    if reason == "TerminalNotDefEqNoRewrite":
        return "proof-composition", "missing-rewrite-or-induction-plan"
    return "unclassified", "manual-triage-required"


def build(
    census: dict[str, Any],
    ranking: dict[str, Any],
    *,
    census_path: Path = CENSUS,
    ranking_path: Path = RANKING,
) -> dict[str, Any]:
    if census.get("kind") != "axeyum-open-ranked-transport-induction-census":
        raise ValueError("input is not a retrieved-induction census")
    if census.get("state") != "train-development-measurement-held-out-excluded":
        raise ValueError("census does not preserve the held-out exclusion boundary")
    if ranking.get("kind") != "axeyum-open-lemma-rewrite-support-ranking":
        raise ValueError("input is not a rewrite-support ranking")
    if census.get("source", {}).get("candidate_ranking", {}).get("sha256") != digest(
        ranking_path
    ):
        raise ValueError("census is not bound to the selected rewrite-support ranking")
    rank_by_fact = {row["fact_id"]: row for row in ranking["goals"]}
    rows = []
    for source in census["outcomes"]:
        fact_id = source["fact_id"]
        if source["evaluation_class"] not in {
            "positive-target",
            "must-decline-control",
        }:
            raise ValueError(f"unknown evaluation class for {fact_id}")
        ranked = rank_by_fact.get(fact_id)
        if ranked is None:
            raise ValueError(f"census fact is absent from ranking: {fact_id}")
        stage, demand = classify(source)
        transports = source.get("candidate_transport", [])
        rows.append(
            {
                "fact_id": fact_id,
                "target_definition": source["target_definition"],
                "evaluation_class": source["evaluation_class"],
                "result": source["result"],
                "reason_kind": source.get("reason_kind"),
                "obstruction_stage": stage,
                "capability_demand": demand,
                "eligible_for_strategy_queue": source["evaluation_class"]
                == "positive-target",
                "primary_candidate_count": ranked["primary_candidate_count"],
                "rewrite_support_candidate_count": ranked[
                    "rewrite_support_candidate_count"
                ],
                "transport": dict(
                    sorted(Counter(item["result"] for item in transports).items())
                ),
                "checked_theorem_dependencies": source.get(
                    "theorem_dependencies", []
                ),
                "axiom_footprint": source.get("axiom_footprint"),
            }
        )
    rows.sort(key=lambda row: row["fact_id"])
    positive = [row for row in rows if row["eligible_for_strategy_queue"]]
    controls = [row for row in rows if not row["eligible_for_strategy_queue"]]
    accepted_controls = [row["fact_id"] for row in controls if row["result"] == "accepted"]
    if accepted_controls:
        raise ValueError(f"must-decline controls were accepted: {accepted_controls}")
    return {
        "schema_version": 1,
        "kind": "axeyum-retrieved-induction-obstruction-projection",
        "state": "measurement-derived-candidate-only",
        "authority": "strategy demand only; no proof, operation, applicability, or fact-transition authority",
        "source": {
            "census_path": str(census_path.relative_to(ROOT)),
            "census_sha256": digest(census_path),
            "ranking_path": str(ranking_path.relative_to(ROOT)),
            "ranking_sha256": digest(ranking_path),
        },
        "census": {
            "rows": len(rows),
            "positive_targets": len(positive),
            "must_decline_controls": len(controls),
            "accepted_positive_targets": sum(
                row["result"] == "accepted" for row in positive
            ),
            "accepted_must_decline_controls": 0,
            "positive_demand": dict(
                sorted(Counter(row["capability_demand"] for row in positive).items())
            ),
        },
        "strategy_queue": [row for row in rows if row["eligible_for_strategy_queue"]],
        "control_observations": controls,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--census", type=Path, default=CENSUS)
    parser.add_argument("--ranking", type=Path, default=RANKING)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    rendered = json.dumps(
        build(
            json.loads(args.census.read_text()),
            json.loads(args.ranking.read_text()),
            census_path=args.census,
            ranking_path=args.ranking,
        ),
        indent=2,
        sort_keys=True,
    ) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            print("RETRIEVED_INDUCTION_OBSTRUCTIONS_ERROR|artifact is stale")
            return 1
    else:
        args.output.write_text(rendered)
    result = json.loads(rendered)
    counts = result["census"]
    print(
        "RETRIEVED_INDUCTION_OBSTRUCTIONS|"
        f"rows={counts['rows']}|positive={counts['positive_targets']}|"
        f"accepted={counts['accepted_positive_targets']}|"
        f"controls={counts['must_decline_controls']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
