#!/usr/bin/env python3
"""Validate and summarize CNF construction and duplicate-origin profiles."""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path
from typing import Any


ARTIFACT_VERSION = 36
REPORT_SCHEMA = "axeyum.cnf-construction-profile-analysis.v2"
INVARIANTS = {
    "non_tautological_attempts_equal_length_buckets",
    "non_tautological_attempts_equal_primary_probes",
    "occupied_probes_partition",
    "duplicates_partition",
    "emitted_partition",
    "tautologies_partition",
}
ORIGIN_INVARIANTS = {
    "duplicate_clauses_equal_rows",
    "duplicate_literals_equal_rows",
    "row_clauses_equal_length_buckets",
    "row_literals_equal_length_buckets",
    "construction_duplicates_equal_origin_duplicates",
    "owner_relations_closed",
}
LENGTH_BUCKETS = ("empty", "unit", "binary", "ternary", "larger")
COUNTER_PATHS = {
    "clause_attempts": ("clause_attempts",),
    "tautological_clauses_skipped": ("tautological_clauses_skipped",),
    "duplicate_clauses_skipped": ("duplicate_clauses_skipped",),
    "clauses_emitted": ("clauses_emitted",),
    "declared_clause_literals": ("detailed_profile", "declared_clause_literals"),
    "visited_clause_literals": ("detailed_profile", "visited_clause_literals"),
    "false_constants_dropped": ("detailed_profile", "false_constants_dropped"),
    "repeated_literals_dropped": ("detailed_profile", "repeated_literals_dropped"),
    "true_constant_tautologies": (
        "detailed_profile",
        "tautologies",
        "true_constant",
    ),
    "complementary_literal_tautologies": (
        "detailed_profile",
        "tautologies",
        "complementary_literal",
    ),
    "canonical_literals": ("detailed_profile", "canonical_literals"),
    "canonical_empty_clauses": (
        "detailed_profile",
        "canonical_clause_lengths",
        "empty",
    ),
    "canonical_unit_clauses": (
        "detailed_profile",
        "canonical_clause_lengths",
        "unit",
    ),
    "canonical_binary_clauses": (
        "detailed_profile",
        "canonical_clause_lengths",
        "binary",
    ),
    "canonical_ternary_clauses": (
        "detailed_profile",
        "canonical_clause_lengths",
        "ternary",
    ),
    "canonical_larger_clauses": (
        "detailed_profile",
        "canonical_clause_lengths",
        "larger",
    ),
    "primary_vacant_probes": ("detailed_profile", "primary_vacant_probes"),
    "primary_occupied_probes": ("detailed_profile", "primary_occupied_probes"),
    "primary_exact_duplicates": (
        "detailed_profile",
        "primary_exact_duplicates",
    ),
    "collision_bucket_comparisons": (
        "detailed_profile",
        "collision_bucket_comparisons",
    ),
    "collision_exact_duplicates": (
        "detailed_profile",
        "collision_exact_duplicates",
    ),
    "collision_inserts": ("detailed_profile", "collision_inserts"),
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def nested(value: dict[str, Any], path: tuple[str, ...], *, label: str) -> Any:
    current: Any = value
    for key in path:
        require(isinstance(current, dict) and key in current, f"{label} lacks {'.'.join(path)}")
        current = current[key]
    return current


def count(value: Any, *, label: str) -> int:
    require(isinstance(value, int) and not isinstance(value, bool) and value >= 0, f"{label} is not a non-negative integer")
    return value


def require_invariants(profile: dict[str, Any], *, label: str) -> None:
    invariants = profile.get("invariants")
    require(isinstance(invariants, dict), f"{label} lacks invariants")
    require(set(invariants) == INVARIANTS, f"{label} invariant set mismatch")
    require(all(value is True for value in invariants.values()), f"{label} has a failed invariant")


def origin_lengths(value: Any, *, label: str) -> dict[str, dict[str, int]]:
    require(isinstance(value, dict), f"{label} lacks duplicate-origin lengths")
    require(set(value) == set(LENGTH_BUCKETS), f"{label} duplicate-origin length set mismatch")
    result = {}
    for bucket in LENGTH_BUCKETS:
        row = value[bucket]
        require(isinstance(row, dict) and set(row) == {"clauses", "literals"}, f"{label}.{bucket} is malformed")
        result[bucket] = {
            "clauses": count(row["clauses"], label=f"{label}.{bucket}.clauses"),
            "literals": count(row["literals"], label=f"{label}.{bucket}.literals"),
        }
    return result


def add_origin_metrics(destination: dict[str, Any], source: dict[str, Any]) -> None:
    destination["duplicate_clauses"] += source["duplicate_clauses"]
    destination["duplicate_canonical_literals"] += source["duplicate_canonical_literals"]
    for bucket in LENGTH_BUCKETS:
        destination["lengths"][bucket]["clauses"] += source["lengths"][bucket]["clauses"]
        destination["lengths"][bucket]["literals"] += source["lengths"][bucket]["literals"]


def empty_origin_metrics() -> dict[str, Any]:
    return {
        "duplicate_clauses": 0,
        "duplicate_canonical_literals": 0,
        "lengths": {
            bucket: {"clauses": 0, "literals": 0} for bucket in LENGTH_BUCKETS
        },
    }


def origin_profile(
    profile: dict[str, Any],
    *,
    expected_duplicate_clauses: int,
    label: str,
) -> tuple[dict[str, Any], dict[tuple[str, str, str], dict[str, Any]]]:
    value = profile.get("duplicate_origins")
    require(isinstance(value, dict), f"{label} lacks duplicate-origin profile")
    require(value.get("profile_complete") is True, f"{label} duplicate-origin profile is incomplete")
    invariants = value.get("invariants")
    require(isinstance(invariants, dict), f"{label} duplicate-origin profile lacks invariants")
    require(set(invariants) == ORIGIN_INVARIANTS, f"{label} duplicate-origin invariant set mismatch")
    require(all(entry is True for entry in invariants.values()), f"{label} duplicate-origin failed invariant")
    totals = {
        "duplicate_clauses": count(value.get("duplicate_clauses"), label=f"{label}.duplicate_clauses"),
        "duplicate_canonical_literals": count(
            value.get("duplicate_canonical_literals"),
            label=f"{label}.duplicate_canonical_literals",
        ),
        "lengths": origin_lengths(value.get("lengths"), label=label),
    }
    require(
        totals["duplicate_clauses"] == expected_duplicate_clauses,
        f"{label} duplicate-origin clause total drift",
    )
    rows = value.get("rows")
    require(isinstance(rows, list), f"{label} duplicate-origin rows are malformed")
    rendered: dict[tuple[str, str, str], dict[str, Any]] = {}
    summed = empty_origin_metrics()
    for index, row in enumerate(rows):
        row_label = f"{label}.duplicate_origins.rows[{index}]"
        require(isinstance(row, dict), f"{row_label} is not an object")
        first = row.get("first_origin")
        duplicate = row.get("duplicate_origin")
        relation = row.get("owner_relation")
        require(isinstance(first, str) and first.count("/") == 3, f"{row_label} first origin is malformed")
        require(isinstance(duplicate, str) and duplicate.count("/") == 3, f"{row_label} duplicate origin is malformed")
        require(relation in {"same", "cross"}, f"{row_label} owner relation is invalid")
        key = (first, duplicate, relation)
        require(key not in rendered, f"{row_label} repeats a duplicate-origin cell")
        metrics = {
            "duplicate_clauses": count(row.get("duplicate_clauses"), label=f"{row_label}.duplicate_clauses"),
            "duplicate_canonical_literals": count(
                row.get("duplicate_canonical_literals"),
                label=f"{row_label}.duplicate_canonical_literals",
            ),
            "lengths": origin_lengths(row.get("lengths"), label=row_label),
        }
        require(metrics["duplicate_clauses"] > 0, f"{row_label} is a zero cell")
        require(
            metrics["duplicate_clauses"]
            == sum(metrics["lengths"][bucket]["clauses"] for bucket in LENGTH_BUCKETS),
            f"{row_label} duplicate-origin clause partition drift",
        )
        require(
            metrics["duplicate_canonical_literals"]
            == sum(metrics["lengths"][bucket]["literals"] for bucket in LENGTH_BUCKETS),
            f"{row_label} duplicate-origin literal partition drift",
        )
        rendered[key] = metrics
        add_origin_metrics(summed, metrics)
    require(summed == totals, f"{label} duplicate-origin rows do not equal totals")
    return totals, rendered


def counters(cnf: dict[str, Any], *, label: str) -> dict[str, int]:
    return {
        name: count(nested(cnf, path, label=label), label=f"{label}.{name}")
        for name, path in COUNTER_PATHS.items()
    }


def add_counts(destination: dict[str, int], source: dict[str, int]) -> None:
    for name, value in source.items():
        destination[name] += value


def normalized_hash(value: str) -> str:
    return value.removeprefix("sha256:")


def analyze_artifact(
    artifact: dict[str, Any],
    *,
    expected_files: int | None = None,
    expected_sat: int | None = None,
    expected_unsat: int | None = None,
    expected_manifest_sha256: str | None = None,
    expected_families: dict[str, int] | None = None,
) -> dict[str, Any]:
    require(artifact.get("version") == ARTIFACT_VERSION, "artifact version mismatch")
    config = artifact.get("config")
    summary = artifact.get("summary")
    instances = artifact.get("instances")
    require(isinstance(config, dict), "artifact lacks config")
    require(isinstance(summary, dict), "artifact lacks summary")
    require(isinstance(instances, list), "artifact lacks instances")
    require(config.get("backend_kind") == "sat-bv", "profile requires sat-bv")
    require(config.get("profile_cnf_construction") is True, "CNF profile was not selected")
    require(config.get("jobs") == 1, "profile requires one benchmark worker")

    files = count(summary.get("files"), label="summary.files")
    sat = count(summary.get("sat"), label="summary.sat")
    unsat = count(summary.get("unsat"), label="summary.unsat")
    require(len(instances) == files, "instance population does not match summary")
    require(sat + unsat == files, "not every query decided")
    for key in ("unknown", "unsupported", "errors", "disagree", "model_replay_failures"):
        require(summary.get(key) == 0, f"summary.{key} is nonzero")
    manifest_summary = summary.get("manifest")
    oracle_summary = summary.get("oracle")
    require(isinstance(manifest_summary, dict), "summary lacks manifest gate")
    require(isinstance(oracle_summary, dict), "summary lacks oracle gate")
    require(manifest_summary.get("compared") == files, "manifest comparison population is incomplete")
    require(manifest_summary.get("agree") == files, "manifest verdict disagreement")
    require(manifest_summary.get("disagree") == 0, "manifest verdict disagreement")
    require(oracle_summary.get("compared") == files, "oracle comparison population is incomplete")
    require(oracle_summary.get("agree") == files, "oracle verdict disagreement")
    require(oracle_summary.get("disagree") == 0, "oracle verdict disagreement")
    require(oracle_summary.get("skipped") == 0, "oracle comparison skipped a query")

    layer = summary.get("layer_attribution")
    require(isinstance(layer, dict), "summary lacks layer attribution")
    require(layer.get("instances") == files, "layer population is incomplete")
    require(layer.get("model_replay_instances") == sat, "SAT replay population is incomplete")
    summary_cnf = nested(layer, ("construction", "cnf"), label="summary")
    require(isinstance(summary_cnf, dict), "summary CNF attribution is malformed")
    summary_profile = summary_cnf.get("detailed_profile")
    require(isinstance(summary_profile, dict), "summary lacks detailed CNF profile")
    require(summary_profile.get("profile_complete") is True, "summary profile is incomplete")
    require(summary_profile.get("profiled_instances") == files, "summary profiled population is incomplete")
    require(summary_profile.get("instances") == files, "summary profile population drift")
    require_invariants(summary_profile, label="summary profile")

    aggregate = defaultdict(int)
    families: dict[str, dict[str, Any]] = {}
    aggregate_origin_totals = empty_origin_metrics()
    aggregate_origin_rows: dict[tuple[str, str, str], dict[str, Any]] = {}
    origin_participation: dict[tuple[str, str, str], set[int]] = defaultdict(set)
    origin_largest_instance: dict[tuple[str, str, str], int] = defaultdict(int)
    origin_families: dict[tuple[str, str, str], dict[str, dict[str, int]]] = defaultdict(
        lambda: defaultdict(lambda: {"sat": 0, "unsat": 0})
    )
    for index, instance in enumerate(instances):
        label = f"instance[{index}]"
        require(isinstance(instance, dict), f"{label} is not an object")
        require(instance.get("outcome") in {"sat", "unsat"}, f"{label} is not decided")
        manifest = instance.get("corpus_manifest")
        require(isinstance(manifest, dict), f"{label} lacks manifest metadata")
        require(manifest.get("decision_agrees") is True, f"{label} disagrees with manifest")
        family = manifest.get("family")
        require(isinstance(family, str) and family, f"{label} lacks a family")
        instance_layer = instance.get("layer_attribution")
        require(isinstance(instance_layer, dict), f"{label} lacks layer attribution")
        cnf = nested(instance_layer, ("construction", "cnf"), label=label)
        require(isinstance(cnf, dict), f"{label} CNF attribution is malformed")
        profile = cnf.get("detailed_profile")
        require(isinstance(profile, dict), f"{label} lacks detailed profile")
        require(profile.get("profile_complete") is True, f"{label} profile is incomplete")
        require_invariants(profile, label=label)
        row_counts = counters(cnf, label=label)
        origin_totals, origin_rows = origin_profile(
            profile,
            expected_duplicate_clauses=row_counts["duplicate_clauses_skipped"],
            label=label,
        )
        add_origin_metrics(aggregate_origin_totals, origin_totals)
        for key, metrics in origin_rows.items():
            aggregate_row = aggregate_origin_rows.setdefault(key, empty_origin_metrics())
            add_origin_metrics(aggregate_row, metrics)
            origin_participation[key].add(index)
            origin_largest_instance[key] = max(
                origin_largest_instance[key], metrics["duplicate_clauses"]
            )
            origin_families[key][family][instance["outcome"]] += metrics[
                "duplicate_clauses"
            ]
        add_counts(aggregate, row_counts)
        row = families.setdefault(
            family,
            {"instances": 0, "sat": 0, "unsat": 0, "counters": defaultdict(int)},
        )
        row["instances"] += 1
        row[instance["outcome"]] += 1
        add_counts(row["counters"], row_counts)

    expected_aggregate = counters(summary_cnf, label="summary")
    require(dict(aggregate) == expected_aggregate, "summary counters do not equal per-instance sums")
    summary_origin_totals, summary_origin_rows = origin_profile(
        summary_profile,
        expected_duplicate_clauses=expected_aggregate["duplicate_clauses_skipped"],
        label="summary",
    )
    require(
        aggregate_origin_totals == summary_origin_totals,
        "summary duplicate-origin totals do not equal per-instance sums",
    )
    require(
        aggregate_origin_rows == summary_origin_rows,
        "summary duplicate-origin rows do not equal per-instance sums",
    )

    if expected_files is not None:
        require(files == expected_files, "file-count gate failed")
    if expected_sat is not None:
        require(sat == expected_sat, "SAT-count gate failed")
    if expected_unsat is not None:
        require(unsat == expected_unsat, "UNSAT-count gate failed")
    manifest_config = config.get("corpus_manifest")
    require(isinstance(manifest_config, dict), "config lacks corpus manifest identity")
    manifest_hash = manifest_config.get("content_hash")
    require(isinstance(manifest_hash, str), "config lacks manifest hash")
    if expected_manifest_sha256 is not None:
        require(
            normalized_hash(manifest_hash) == normalized_hash(expected_manifest_sha256),
            "manifest hash gate failed",
        )
    observed_family_counts = {name: row["instances"] for name, row in families.items()}
    if expected_families is not None:
        require(observed_family_counts == expected_families, "family-count gate failed")

    rendered_families = {
        name: {
            "instances": row["instances"],
            "sat": row["sat"],
            "unsat": row["unsat"],
            "counters": dict(row["counters"]),
        }
        for name, row in sorted(families.items())
    }
    rendered_origin_rows = []
    by_duplicate_origin: dict[str, dict[str, Any]] = {}
    eligible_cells = []
    all_duplicate_clauses = aggregate_origin_totals["duplicate_clauses"]
    for key, metrics in sorted(aggregate_origin_rows.items()):
        clauses = metrics["duplicate_clauses"]
        duplicate_origin_metrics = by_duplicate_origin.setdefault(
            key[1], empty_origin_metrics()
        )
        add_origin_metrics(duplicate_origin_metrics, metrics)
        participating_instances = len(origin_participation[key])
        largest_instance = origin_largest_instance[key]
        selection_eligible = (
            clauses * 2 >= all_duplicate_clauses
            and participating_instances >= 10
            and largest_instance * 2 <= clauses
        )
        if selection_eligible:
            eligible_cells.append(
                {
                    "first_origin": key[0],
                    "duplicate_origin": key[1],
                    "owner_relation": key[2],
                }
            )
        rendered_origin_rows.append(
            {
                "first_origin": key[0],
                "duplicate_origin": key[1],
                "owner_relation": key[2],
                **metrics,
                "participating_instances": participating_instances,
                "largest_single_instance_clauses": largest_instance,
                "largest_instance_share": (
                    largest_instance / clauses if clauses else None
                ),
                "share_of_all_duplicates": (
                    clauses / all_duplicate_clauses if all_duplicate_clauses else None
                ),
                "selection_eligible": selection_eligible,
                "families": {
                    family: dict(outcomes)
                    for family, outcomes in sorted(origin_families[key].items())
                },
            }
        )
    return {
        "schema": REPORT_SCHEMA,
        "accepted": True,
        "artifact": {
            "version": ARTIFACT_VERSION,
            "corpus_hash": config.get("corpus_hash"),
            "manifest_sha256": manifest_hash,
            "config_hash": config.get("config_hash"),
        },
        "population": {"files": files, "sat": sat, "unsat": unsat},
        "aggregate": dict(aggregate),
        "duplicate_origins": {
            **aggregate_origin_totals,
            "rows": rendered_origin_rows,
            "by_duplicate_origin": {
                origin: metrics
                for origin, metrics in sorted(by_duplicate_origin.items())
            },
            "eligible_cells": eligible_cells,
            "selection_rule": {
                "minimum_share_of_all_duplicates": 0.5,
                "minimum_participating_instances": 10,
                "maximum_largest_instance_share": 0.5,
            },
        },
        "families": rendered_families,
        "all_profile_invariants_hold": True,
        "claim_limits": [
            "Profiled timing is diagnostic and is not a production performance result.",
            "Work counts attribute construction operations but do not alone prove an optimization will improve wall time.",
            "The report selects no optimization.",
        ],
    }


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as source:
        value = json.load(source)
    if not isinstance(value, dict):
        raise RuntimeError(f"expected JSON object: {path}")
    return value


def family_count(value: str) -> tuple[str, int]:
    name, separator, raw_count = value.partition("=")
    if not separator or not name:
        raise argparse.ArgumentTypeError("family counts must use NAME=COUNT")
    try:
        parsed = int(raw_count)
    except ValueError as error:
        raise argparse.ArgumentTypeError("family count must be an integer") from error
    if parsed < 0:
        raise argparse.ArgumentTypeError("family count must be non-negative")
    return name, parsed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifact", type=Path)
    parser.add_argument("--expected-files", type=int)
    parser.add_argument("--expected-sat", type=int)
    parser.add_argument("--expected-unsat", type=int)
    parser.add_argument("--expected-manifest-sha256")
    parser.add_argument("--expected-family", action="append", type=family_count, default=[])
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    expected_families = dict(args.expected_family) if args.expected_family else None
    require(
        expected_families is None or len(expected_families) == len(args.expected_family),
        "duplicate expected family",
    )
    report = analyze_artifact(
        load_json(args.artifact),
        expected_files=args.expected_files,
        expected_sat=args.expected_sat,
        expected_unsat=args.expected_unsat,
        expected_manifest_sha256=args.expected_manifest_sha256,
        expected_families=expected_families,
    )
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.out is None:
        print(rendered, end="")
    else:
        args.out.write_text(rendered, encoding="utf-8")


if __name__ == "__main__":
    main()
