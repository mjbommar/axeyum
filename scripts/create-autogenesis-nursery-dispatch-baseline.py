#!/usr/bin/env python3
"""Measure preregistered train/development dispatch readiness without running proofs."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from collections import Counter, defaultdict
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
OPERATIONS = ROOT / "artifacts/autogenesis/operations.json"
FACTS = ROOT / "artifacts/facts"
OUTPUT = ROOT / "artifacts/autogenesis/mathlib-nursery-dispatch-baseline-v1.json"
STATEMENT_ADAPTERS = ROOT / "artifacts/autogenesis"
PARTITIONS = {"train", "development"}


class BaselineError(RuntimeError):
    """The dispatch baseline is stale or would inspect protected outcomes."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BaselineError(f"{path.relative_to(ROOT)} is not an object")
    return value


def classify(
    fact: dict[str, Any], operations: list[dict[str, Any]], adapted_fact_ids: set[str] | None = None
) -> tuple[str, list[str]]:
    language = fact["formal"]["language"]
    fragment = fact["formal"]["fragment"]
    exact_fact = [op for op in operations if fact["id"] in op["applicability"]["fact_ids"]]
    exact = [
        op for op in exact_fact
        if language in op["applicability"]["formal_languages"]
        and fragment in op["applicability"]["fragments"]
    ]
    if exact:
        return "dispatchable", sorted(op["id"] for op in exact)
    if fact["id"] in (adapted_fact_ids or set()):
        return "statement-adapter-ready:no-authoritative-producer", []
    if not any(language in op["applicability"]["formal_languages"] for op in operations):
        return f"unsupported-formal-language:{language}", []
    if exact_fact:
        return "exact-operation-contract-mismatch", sorted(op["id"] for op in exact_fact)
    return "no-exact-authoritative-operation", []


def build(nursery: dict[str, Any], registry: dict[str, Any], facts: dict[str, dict[str, Any]]) -> dict[str, Any]:
    if nursery.get("state") != "frozen-evaluation":
        raise BaselineError("nursery is not frozen")
    operations = [op for op in registry.get("operations", []) if op.get("scope") == "authoritative"]
    adapter_manifests = [
        load(path)
        for path in sorted(STATEMENT_ADAPTERS.glob("*-statement-adapter-v1.json"))
    ]
    adapted_fact_ids = {
        manifest["source_fact_id"]
        for manifest in adapter_manifests
        if manifest.get("state") == "independent-kernel-goal-admitted-proof-free"
    }
    entries = [row for row in nursery.get("entries", []) if row.get("partition") in PARTITIONS]
    if len(entries) != 138:
        raise BaselineError(f"expected 138 train/development entries, found {len(entries)}")
    if any(row.get("partition") == "held-out" for row in entries):
        raise BaselineError("held-out entry entered the baseline")

    rows: list[dict[str, Any]] = []
    by_family: dict[str, Counter[str]] = defaultdict(Counter)
    reasons: Counter[str] = Counter()
    for entry in sorted(entries, key=lambda row: row["fact_id"]):
        fact = facts.get(entry["fact_id"])
        if fact is None:
            raise BaselineError(f"missing fact {entry['fact_id']}")
        reason, operation_ids = classify(fact, operations, adapted_fact_ids)
        outcome = "eligible-for-dispatch" if reason == "dispatchable" else "declined-before-execution"
        reasons[reason] += 1
        by_family[entry["family"]][reason] += 1
        rows.append({
            "fact_id": entry["fact_id"],
            "family": entry["family"],
            "partition": entry["partition"],
            "formal_language": fact["formal"]["language"],
            "fragment": fact["formal"]["fragment"],
            "outcome": outcome,
            "decline_reason": None if reason == "dispatchable" else reason,
            "registered_operation_ids": operation_ids,
            "executor_budget_consumed": 0,
            "statement_adapter_ready": entry["fact_id"] in adapted_fact_ids,
        })
    result: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-nursery-dispatch-baseline",
        "state": "pre-execution-capability-census",
        "authority": {
            "nursery_sha256": digest(nursery),
            "operation_registry_sha256": digest(registry),
            "partitions_inspected": ["development", "train"],
            "held_out_inspected": False,
            "proof_bodies_accessed": False,
            "target_outcomes_accessed": False,
            "statement_adapter_fact_ids": sorted(adapted_fact_ids & {row["fact_id"] for row in entries}),
        },
        "budget": {
            "candidate_inspection_limit": 138,
            "executor_invocations": 0,
            "executor_budget_consumed": 0,
        },
        "coverage": {
            "candidates": len(rows),
            "eligible_for_dispatch": sum(row["outcome"] == "eligible-for-dispatch" for row in rows),
            "declined_before_execution": sum(row["outcome"] == "declined-before-execution" for row in rows),
            "decline_reasons": dict(sorted(reasons.items())),
            "families": {
                family: dict(sorted(counts.items())) for family, counts in sorted(by_family.items())
            },
        },
        "rows": rows,
        "interpretation": "This is a dispatch-contract census, not a proof episode or theorem outcome. A pre-execution decline consumes no producer budget and earns no proof credit.",
    }
    result["baseline_sha256"] = digest(result)
    return result


def load_facts() -> dict[str, dict[str, Any]]:
    return {fact["id"]: fact for fact in (load(path) for path in sorted(FACTS.glob("*.json")))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        expected = build(load(NURSERY), load(OPERATIONS), load_facts())
        rendered = json.dumps(expected, indent=2, ensure_ascii=False) + "\n"
        if args.check:
            if not OUTPUT.exists() or OUTPUT.read_text() != rendered:
                raise BaselineError("dispatch baseline is stale; regenerate without --check")
        else:
            OUTPUT.write_text(rendered)
        print(
            "AUTOGENESIS_NURSERY_DISPATCH_BASELINE_OK|"
            f"{expected['baseline_sha256']}|candidates={expected['coverage']['candidates']}|"
            f"dispatchable={expected['coverage']['eligible_for_dispatch']}|"
            f"declined={expected['coverage']['declined_before_execution']}"
        )
    except (OSError, json.JSONDecodeError, KeyError, BaselineError) as error:
        print(f"autogenesis-nursery-dispatch-baseline: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
