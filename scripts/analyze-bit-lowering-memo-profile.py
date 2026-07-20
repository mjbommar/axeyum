#!/usr/bin/env python3
"""Validate ADR-0300's v39 memo profile and optional dense comparison."""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any


SCHEMA = "axeyum.bit-lowering-memo-profile-analysis.v1"
ARTIFACT_VERSION = 39
MANIFEST_SHA256 = "7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064"
FAMILIES = {
    "arithmetic": 36,
    "comparison": 12,
    "mixed": 7,
    "register-slice": 52,
    "slice-partial": 54,
    "trivial": 1,
}
REPRESENTATIONS = {"btree-v1", "dense-v1"}
DIGEST = re.compile(r"[0-9a-f]{16}")
MEMO_NUMERIC_FIELDS = (
    "source_terms",
    "slots",
    "occupied",
    "lookups",
    "hits",
    "writes",
    "payload_literals",
    "payload_capacity_literals",
    "logical_header_bytes",
    "logical_payload_bytes",
    "logical_total_bytes",
    "payload_capacity_bytes",
    "root_bits",
    "expected_root_bits",
)
MEMO_FIELDS = {
    "profile_complete",
    "representation",
    *MEMO_NUMERIC_FIELDS,
    "header_accounting",
    "digests",
    "invariants",
}
INVARIANTS = {
    "producer",
    "representation_shape",
    "hits_within_lookups",
    "writes_equal_occupied",
    "payload_matches_term_bits",
    "capacity_covers_payload",
    "logical_total_partitions",
    "root_widths_match",
    "all_hold",
}
AGGREGATE_FIELDS = {
    "profile_complete",
    "profiled_samples",
    "digest_samples",
    "samples",
    "representation_counts",
    *MEMO_NUMERIC_FIELDS,
    "all_instance_invariants_hold",
}
IDENTITY_FIELDS = (
    "file",
    "outcome",
    "expected",
    "assertions",
    "dag_nodes",
    "tree_nodes",
    "max_depth",
    "distinct_symbols",
    "query_shape",
    "query_plan",
    "corpus_manifest",
)
NEUTRAL_MEMO_FIELDS = (
    "source_terms",
    "occupied",
    "lookups",
    "hits",
    "writes",
    "payload_literals",
    "payload_capacity_literals",
    "logical_payload_bytes",
    "payload_capacity_bytes",
    "root_bits",
    "expected_root_bits",
)
REPRESENTATION_BACKEND_FIELDS = {
    "bit_lowering_memo_representation",
    "bit_lowering_memo_slots",
    "bit_lowering_memo_logical_header_bytes",
    "bit_lowering_memo_logical_total_bytes",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def count(value: Any, *, label: str) -> int:
    require(
        isinstance(value, int) and not isinstance(value, bool) and value >= 0,
        f"{label} is not a non-negative integer",
    )
    return value


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as source:
        value = json.load(source)
    require(isinstance(value, dict), f"expected JSON object: {path}")
    return value


def validate_config(artifact: dict[str, Any], *, manifest_sha256: str) -> None:
    require(artifact.get("version") == ARTIFACT_VERSION, "artifact version is not v39")
    config = artifact.get("config")
    require(isinstance(config, dict), "artifact config is missing")
    expected = {
        "backend_kind": "sat-bv",
        "logic": "QF_BV",
        "jobs": 1,
        "manifest_validation_jobs": 1,
        "profile_bit_demand": True,
        "demand_bit_slicing": False,
        "range_demand_slicing": False,
        "preprocess": False,
        "compare_z3": True,
        "require_in_process_z3": True,
        "require_reproducible_run": True,
        "require_deterministic_resources": True,
        "timeout_ms": 10_000,
        "resource_limit": 2_000_000,
        "node_budget": 300_000,
        "cnf_variable_budget": 3_000_000,
        "cnf_clause_budget": 8_000_000,
        "min_decided_percent": 100.0,
    }
    for key, value in expected.items():
        require(config.get(key) == value, f"config.{key} drift")
    rewrite = config.get("rewrite")
    require(isinstance(rewrite, dict) and rewrite.get("mode") == "off", "rewrite is not off")
    query_plan = config.get("query_plan")
    require(
        isinstance(query_plan, dict) and query_plan.get("mode") == "full",
        "query plan is not full",
    )
    manifest = config.get("corpus_manifest")
    require(isinstance(manifest, dict), "config corpus manifest is missing")
    require(
        manifest.get("content_hash") == f"sha256:{manifest_sha256}",
        "manifest digest drift",
    )


def validate_summary(summary: Any, *, files: int, sat: int, unsat: int) -> None:
    require(isinstance(summary, dict), "artifact summary is missing")
    expected = {
        "files": files,
        "sat": sat,
        "unsat": unsat,
        "decided": files,
        "unknown": 0,
        "unsupported": 0,
        "errors": 0,
        "disagree": 0,
        "model_replay_failures": 0,
    }
    for key, value in expected.items():
        require(summary.get(key) == value, f"summary.{key} drift")
    require(summary.get("decided_percent") == 100.0, "summary is not 100% decided")
    manifest = summary.get("manifest")
    require(isinstance(manifest, dict), "summary manifest is missing")
    for key, value in {"expected": files, "compared": files, "agree": files, "disagree": 0}.items():
        require(manifest.get(key) == value, f"summary.manifest.{key} drift")
    oracle = summary.get("oracle")
    require(isinstance(oracle, dict) and oracle.get("enabled") is True, "oracle is disabled")
    for key, value in {"compared": files, "agree": files, "disagree": 0, "skipped": 0}.items():
        require(oracle.get(key) == value, f"summary.oracle.{key} drift")
    population = oracle.get("decision_population")
    require(isinstance(population, dict), "oracle decision population is missing")
    for key, value in {
        "accounted": files,
        "both_decided": files,
        "axeyum_only_decided": 0,
        "z3_only_decided": 0,
        "neither_decided": 0,
    }.items():
        require(population.get(key) == value, f"oracle population {key} drift")


def validate_memo(value: Any, *, representation: str, label: str) -> dict[str, int]:
    require(isinstance(value, dict), f"{label} memo profile is missing")
    require(set(value) == MEMO_FIELDS, f"{label} memo field set mismatch")
    require(value.get("profile_complete") is True, f"{label} memo profile is incomplete")
    require(representation in REPRESENTATIONS, "expected representation is unknown")
    require(value.get("representation") == representation, f"{label} representation drift")
    numeric = {
        key: count(value.get(key), label=f"{label}.{key}") for key in MEMO_NUMERIC_FIELDS
    }
    invariants = value.get("invariants")
    require(isinstance(invariants, dict), f"{label} invariants are missing")
    require(set(invariants) == INVARIANTS, f"{label} invariant set mismatch")
    require(all(entry is True for entry in invariants.values()), f"{label} invariant failed")
    digests = value.get("digests")
    require(isinstance(digests, dict), f"{label} digests are missing")
    require(set(digests) == {"lowering_fnv64", "cnf_fnv64"}, f"{label} digest set mismatch")
    require(DIGEST.fullmatch(digests["lowering_fnv64"]) is not None, f"{label} lowering digest malformed")
    require(DIGEST.fullmatch(digests["cnf_fnv64"]) is not None, f"{label} CNF digest malformed")
    require(numeric["hits"] <= numeric["lookups"], f"{label} hits exceed lookups")
    require(numeric["writes"] == numeric["occupied"], f"{label} writes differ from occupied")
    require(
        numeric["payload_capacity_literals"] >= numeric["payload_literals"],
        f"{label} payload capacity is too small",
    )
    require(
        numeric["logical_total_bytes"]
        == numeric["logical_header_bytes"] + numeric["logical_payload_bytes"],
        f"{label} logical byte partition failed",
    )
    require(numeric["root_bits"] == numeric["expected_root_bits"], f"{label} root width drift")
    if representation == "btree-v1":
        require(numeric["slots"] == numeric["occupied"], f"{label} BTree shape drift")
    else:
        require(numeric["slots"] == numeric["source_terms"], f"{label} dense slot drift")
        require(numeric["occupied"] <= numeric["slots"], f"{label} dense occupancy drift")
    return numeric


def validate_aggregate(
    value: Any,
    *,
    representation: str,
    rows: list[dict[str, int]],
) -> dict[str, int]:
    require(isinstance(value, dict), "summary memo aggregate is missing")
    require(set(value) == AGGREGATE_FIELDS, "summary memo aggregate field set mismatch")
    samples = len(rows)
    require(value.get("profile_complete") is True, "aggregate profile is incomplete")
    for key in ("profiled_samples", "digest_samples", "samples"):
        require(value.get(key) == samples, f"aggregate {key} drift")
    representations = value.get("representation_counts")
    require(
        isinstance(representations, dict)
        and set(representations) == {"btree-v1", "dense-v1", "unavailable"},
        "aggregate representation counts are malformed",
    )
    expected_counts = {"btree-v1": 0, "dense-v1": 0, "unavailable": 0}
    expected_counts[representation] = samples
    require(representations == expected_counts, "aggregate representation count drift")
    totals = {key: sum(row[key] for row in rows) for key in MEMO_NUMERIC_FIELDS}
    for key, expected in totals.items():
        require(count(value.get(key), label=f"aggregate.{key}") == expected, f"aggregate {key} drift")
    require(value.get("all_instance_invariants_hold") is True, "aggregate invariant failed")
    return totals


def analyze_artifact(
    artifact: dict[str, Any],
    *,
    expected_files: int,
    expected_sat: int,
    expected_unsat: int,
    expected_manifest_sha256: str,
    expected_families: dict[str, int],
    expected_representation: str,
) -> dict[str, Any]:
    validate_config(artifact, manifest_sha256=expected_manifest_sha256)
    summary = artifact.get("summary")
    validate_summary(summary, files=expected_files, sat=expected_sat, unsat=expected_unsat)
    instances = artifact.get("instances")
    require(isinstance(instances, list), "artifact instances are missing")
    require(len(instances) == expected_files, "instance population drift")
    files: set[str] = set()
    families: Counter[str] = Counter()
    memo_rows: list[dict[str, int]] = []
    outcomes: Counter[str] = Counter()
    for index, row in enumerate(instances):
        label = f"instances[{index}]"
        require(isinstance(row, dict), f"{label} is not an object")
        file_name = row.get("file")
        require(isinstance(file_name, str) and file_name not in files, f"{label} file is invalid or duplicate")
        files.add(file_name)
        outcome = row.get("outcome")
        require(outcome in {"sat", "unsat"}, f"{label} is not decided")
        outcomes[outcome] += 1
        manifest = row.get("corpus_manifest")
        require(isinstance(manifest, dict), f"{label} manifest row is missing")
        require(manifest.get("expected") == outcome, f"{label} manifest verdict drift")
        require(manifest.get("decision_compared") is True, f"{label} manifest was not compared")
        require(manifest.get("decision_agrees") is True, f"{label} manifest disagreement")
        family = manifest.get("family")
        require(isinstance(family, str), f"{label} family is missing")
        families[family] += 1
        oracle = row.get("oracle")
        require(isinstance(oracle, dict) and oracle.get("enabled") is True, f"{label} oracle is disabled")
        require(oracle.get("outcome") == outcome, f"{label} oracle verdict drift")
        require(oracle.get("decision_compared") is True, f"{label} oracle was not compared")
        require(oracle.get("decision_agrees") is True, f"{label} oracle disagreement")
        layer = row.get("layer_attribution")
        require(isinstance(layer, dict), f"{label} layer attribution is missing")
        memo_rows.append(
            validate_memo(
                layer.get("bit_lowering_memo"),
                representation=expected_representation,
                label=label,
            )
        )
    require(outcomes == Counter({"sat": expected_sat, "unsat": expected_unsat}), "instance outcome counts drift")
    require(dict(families) == expected_families, "instance family counts drift")
    aggregate = summary.get("layer_attribution")
    require(isinstance(aggregate, dict), "summary layer attribution is missing")
    totals = validate_aggregate(
        aggregate.get("bit_lowering_memo"),
        representation=expected_representation,
        rows=memo_rows,
    )
    return {
        "schema": SCHEMA,
        "accepted": True,
        "representation": expected_representation,
        "population": {"files": expected_files, "sat": expected_sat, "unsat": expected_unsat},
        "families": dict(sorted(families.items())),
        "memo_totals": totals,
        "per_instance_invariants_hold": True,
        "oracle_and_manifest_agreement": True,
    }


def structural_backend_stats(row: dict[str, Any]) -> dict[str, Any]:
    stats = row.get("backend_stats")
    require(isinstance(stats, dict), "instance backend stats are missing")
    return {
        key: value
        for key, value in stats.items()
        if not key.endswith("_ms") and key not in REPRESENTATION_BACKEND_FIELDS
    }


def compare_artifacts(
    baseline: dict[str, Any],
    candidate: dict[str, Any],
    baseline_report: dict[str, Any],
    candidate_report: dict[str, Any],
) -> dict[str, Any]:
    for key in ("config_hash", "corpus_hash"):
        require(candidate["config"].get(key) == baseline["config"].get(key), f"{key} drift")
    before_environment = baseline["config"].get("experiment", {}).get("environment_hash")
    after_environment = candidate["config"].get("experiment", {}).get("environment_hash")
    require(after_environment == before_environment, "environment hash drift")
    before_rows = baseline["instances"]
    after_rows = candidate["instances"]
    require(len(after_rows) == len(before_rows), "candidate population drift")
    for index, (before, after) in enumerate(zip(before_rows, after_rows, strict=True)):
        label = f"instances[{index}]"
        for key in IDENTITY_FIELDS:
            require(after.get(key) == before.get(key), f"{label} {key} drift")
        before_oracle = before.get("oracle", {})
        after_oracle = after.get("oracle", {})
        for key in ("backend_kind", "enabled", "outcome", "decision_compared", "decision_agrees", "decision_population", "query_boundary"):
            require(after_oracle.get(key) == before_oracle.get(key), f"{label} oracle {key} drift")
        require(structural_backend_stats(after) == structural_backend_stats(before), f"{label} backend structure drift")
        before_memo = before["layer_attribution"]["bit_lowering_memo"]
        after_memo = after["layer_attribution"]["bit_lowering_memo"]
        for key in NEUTRAL_MEMO_FIELDS:
            require(after_memo[key] == before_memo[key], f"{label} memo {key} drift")
        require(after_memo["digests"] == before_memo["digests"], f"{label} structure digest drift")
    baseline_bytes = baseline_report["memo_totals"]["logical_total_bytes"]
    candidate_bytes = candidate_report["memo_totals"]["logical_total_bytes"]
    require(candidate_bytes * 10 <= baseline_bytes * 11, "candidate logical memo bytes exceed 110%")
    return {
        "schema": SCHEMA,
        "accepted": True,
        "baseline": baseline_report,
        "candidate": candidate_report,
        "per_instance_structure_preserved": True,
        "logical_bytes_within_gate": True,
        "timing_authorized": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact", type=Path, required=True)
    parser.add_argument("--candidate", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--expected-files", type=int, default=162)
    parser.add_argument("--expected-sat", type=int, default=88)
    parser.add_argument("--expected-unsat", type=int, default=74)
    parser.add_argument("--expected-manifest-sha256", default=MANIFEST_SHA256)
    parser.add_argument("--expected-representation", default="btree-v1")
    parser.add_argument("--candidate-representation", default="dense-v1")
    args = parser.parse_args()
    baseline = load_json(args.artifact)
    baseline_report = analyze_artifact(
        baseline,
        expected_files=args.expected_files,
        expected_sat=args.expected_sat,
        expected_unsat=args.expected_unsat,
        expected_manifest_sha256=args.expected_manifest_sha256,
        expected_families=FAMILIES,
        expected_representation=args.expected_representation,
    )
    report = baseline_report
    if args.candidate is not None:
        candidate = load_json(args.candidate)
        candidate_report = analyze_artifact(
            candidate,
            expected_files=args.expected_files,
            expected_sat=args.expected_sat,
            expected_unsat=args.expected_unsat,
            expected_manifest_sha256=args.expected_manifest_sha256,
            expected_families=FAMILIES,
            expected_representation=args.candidate_representation,
        )
        report = compare_artifacts(baseline, candidate, baseline_report, candidate_report)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
