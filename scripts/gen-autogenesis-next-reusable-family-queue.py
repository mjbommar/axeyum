#!/usr/bin/env python3
"""Rank ready mathematical families by distance to reusable production."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
from collections import Counter, defaultdict
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FRONTIER = ROOT / "artifacts/autogenesis/producer-evaluation-frontier-v1.json"
STRATEGY = ROOT / "artifacts/autogenesis/retrieved-induction-obstruction-projection-v1.json"
BINOMIAL_ARROW = ROOT / "artifacts/autogenesis/binomial-arrow-retrieved-induction-census-v1.json"
BITWISE = ROOT / "artifacts/autogenesis/bitwise-clean-family-projection-v1.json"
OPERATIONS = ROOT / "artifacts/autogenesis/operations.json"
DEFAULT_OUTPUT = ROOT / "artifacts/autogenesis/next-reusable-family-queue-v1.json"


class FamilyQueueError(RuntimeError):
    """The family queue cannot be derived from its checked inputs."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise FamilyQueueError(f"expected JSON object: {path}")
    return value


def classify(demands: Counter[str], accepted: int, measured: int) -> tuple[int, str, str]:
    if accepted >= 3:
        return (
            0,
            "operation-integration-ready",
            "register the unchanged producer over at least three checked targets",
        )
    if accepted:
        return (
            1,
            "expand-unchanged-producer",
            "convert two more siblings with the already accepted producer contract",
        )
    if demands["missing-rewrite-or-induction-plan"] >= 3:
        return (
            2,
            "shared-proof-composition",
            "add one target-agnostic rewrite or induction plan and rerun the family",
        )
    if demands["non-equality-terminal-family"] >= 3:
        return (
            3,
            "shared-producer-grammar",
            "add one reusable terminal relation family and rerun unchanged retrieval",
        )
    if demands["type-slice-generalization"] >= 3:
        return (
            4,
            "shared-statement-contract",
            "complete one shared semantic contract and rerun the family",
        )
    if measured == 0:
        return (
            5,
            "measurement-missing",
            "run the current producer protocol over every ready sibling before implementation",
        )
    return (
        6,
        "fragmented-obstructions",
        "retain the measured declines until one obstruction reaches three siblings",
    )


def demand_for_outcome(row: dict[str, Any]) -> str:
    if row["result"] == "accepted":
        return "authoritative-operation-integration"
    if row["result"] == "import_rejected":
        return "type-slice-generalization"
    return {
        "NotEqualityGoal": "non-equality-terminal-family",
        "BinderBudgetExceeded": "binder-or-generalization",
        "TerminalNotDefEqNoRewrite": "missing-rewrite-or-induction-plan",
    }.get(row.get("reason_kind"), "manual-triage-required")


def build() -> dict[str, Any]:
    frontier = load(FRONTIER)
    strategy = load(STRATEGY)
    binomial_arrow = load(BINOMIAL_ARROW)
    bitwise = load(BITWISE)
    operations = load(OPERATIONS)
    controls = set(frontier["must_decline_control_fact_ids"])
    strategy_by_fact = {
        row["fact_id"]: row
        for row in strategy["strategy_queue"]
        if row.get("evaluation_class") == "positive-target"
    }
    for outcome in binomial_arrow["outcomes"]:
        fact_id = outcome["fact_id"]
        if fact_id in strategy_by_fact:
            raise FamilyQueueError(f"duplicate measured producer outcome: {fact_id}")
        if outcome.get("evaluation_class") != "positive-target":
            raise FamilyQueueError(f"binomial measurement is not a positive target: {fact_id}")
        strategy_by_fact[fact_id] = {
            "fact_id": fact_id,
            "result": outcome["result"],
            "capability_demand": demand_for_outcome(outcome),
        }
    registered = {
        fact_id
        for operation in operations["operations"]
        if operation.get("scope") == "authoritative"
        for fact_id in operation["applicability"]["fact_ids"]
    }
    analogue_facts = {
        row["fact_id"]
        for row in bitwise["rows"]
        if row.get("relationship") == "target-owned-semantic-analogue"
    }

    family_facts: dict[str, set[str]] = defaultdict(set)
    family_components: dict[str, set[str]] = defaultdict(set)
    family_partitions: dict[str, set[str]] = defaultdict(set)
    family_shapes: dict[str, set[str]] = defaultdict(set)
    for group in frontier["groups"]:
        family = group["family"]
        facts = set(group["fact_ids"]).difference(controls)
        family_facts[family].update(facts)
        if facts:
            family_components[family].add(group["dependency_component_id"])
            family_partitions[family].add(group["partition"])
            family_shapes[family].add(group["statement_shape"])

    rows = []
    for family, facts in family_facts.items():
        if not facts:
            continue
        measured_rows = [
            strategy_by_fact[fact] for fact in sorted(facts) if fact in strategy_by_fact
        ]
        demands = Counter(row["capability_demand"] for row in measured_rows)
        results = Counter(row["result"] for row in measured_rows)
        accepted_ids = sorted(
            row["fact_id"] for row in measured_rows if row["result"] == "accepted"
        )
        rank, state, next_action = classify(demands, len(accepted_ids), len(measured_rows))
        rows.append(
            {
                "family": family,
                "priority_class": rank,
                "state": state,
                "next_action": next_action,
                "ready_fact_count": len(facts),
                "ready_fact_ids": sorted(facts),
                "dependency_components": len(family_components[family]),
                "partitions": sorted(family_partitions[family]),
                "statement_shapes": sorted(family_shapes[family]),
                "measured_fact_count": len(measured_rows),
                "unmeasured_fact_count": len(facts) - len(measured_rows),
                "accepted_fact_ids": accepted_ids,
                "producer_results": dict(sorted(results.items())),
                "capability_demands": dict(sorted(demands.items())),
                "target_owned_semantic_analogue_fact_ids": sorted(
                    facts.intersection(analogue_facts)
                ),
                "already_registered_fact_ids": sorted(facts.intersection(registered)),
            }
        )
    rows.sort(
        key=lambda row: (
            row["priority_class"],
            -len(row["accepted_fact_ids"]),
            -row["measured_fact_count"],
            -row["ready_fact_count"],
            row["family"],
        )
    )
    for index, row in enumerate(rows, 1):
        row["rank"] = index

    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-next-reusable-family-queue",
        "authority": "planning projection only; no proof, operation applicability, dispatch, or admission authority",
        "derivation": {
            "producer_evaluation_frontier": {
                "path": FRONTIER.relative_to(ROOT).as_posix(),
                "sha256": hashlib.sha256(FRONTIER.read_bytes()).hexdigest(),
            },
            "retrieved_induction_obstructions": {
                "path": STRATEGY.relative_to(ROOT).as_posix(),
                "sha256": hashlib.sha256(STRATEGY.read_bytes()).hexdigest(),
            },
            "binomial_arrow_retrieved_induction": {
                "path": BINOMIAL_ARROW.relative_to(ROOT).as_posix(),
                "sha256": hashlib.sha256(BINOMIAL_ARROW.read_bytes()).hexdigest(),
            },
            "bitwise_clean_family": {
                "path": BITWISE.relative_to(ROOT).as_posix(),
                "sha256": hashlib.sha256(BITWISE.read_bytes()).hexdigest(),
            },
            "operations": {
                "path": OPERATIONS.relative_to(ROOT).as_posix(),
                "sha256": hashlib.sha256(OPERATIONS.read_bytes()).hexdigest(),
            },
            "ordering": "priority class, accepted count descending, measured count descending, ready count descending, family",
            "reusable_operation_bar": 3,
        },
        "census": {
            "families": len(rows),
            "ready_non_control_facts": sum(row["ready_fact_count"] for row in rows),
            "measured_facts": sum(row["measured_fact_count"] for row in rows),
            "unmeasured_facts": sum(row["unmeasured_fact_count"] for row in rows),
            "accepted_ready_facts": sum(len(row["accepted_fact_ids"]) for row in rows),
            "operation_integration_ready_families": sum(row["priority_class"] == 0 for row in rows),
        },
        "rows": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=pathlib.Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    document = build()
    rendered = json.dumps(document, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            raise FamilyQueueError("next reusable family queue is stale")
    else:
        args.output.write_text(rendered)
    first = document["rows"][0]
    print(
        f"AUTOGENESIS_NEXT_FAMILY|families={document['census']['families']}|"
        f"ready={document['census']['ready_non_control_facts']}|"
        f"measured={document['census']['measured_facts']}|"
        f"next={first['family']}|state={first['state']}"
    )


if __name__ == "__main__":
    try:
        main()
    except (FamilyQueueError, OSError, KeyError, TypeError, ValueError) as error:
        print(f"AUTOGENESIS_NEXT_FAMILY_ERROR|{error}")
        raise SystemExit(1)
