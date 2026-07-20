#!/usr/bin/env python3
"""Validate and summarize CNF construction and duplicate-origin profiles."""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path
from typing import Any


SUPPORTED_ARTIFACT_VERSIONS = {36, 37, 38}
PARITY_OVERLAP_ARTIFACT_VERSION = 37
FLAT_STORAGE_ARTIFACT_VERSION = 38
REPORT_SCHEMA = "axeyum.cnf-construction-profile-analysis.v3"
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
PARITY_INVARIANTS = {
    "duplicate_clauses_equal_rows",
    "duplicate_literals_equal_rows",
    "row_clauses_equal_length_buckets",
    "row_literals_equal_length_buckets",
    "origin_subset_equal_overlap",
    "relations_closed",
}
PARITY_RELATIONS = {"within_leaf", "cross_leaf_same_owner", "cross_owner"}
PARITY_SHAPE = re.compile(r"a([1-3])-f([0-3])-t([0-3])-d([0-3])-r([0-3])-x([0-3])")
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
STORAGE_FIELDS = (
    "formula_clauses",
    "formula_literals",
    "clause_end_logical_bytes",
    "literal_logical_bytes",
    "arena_logical_bytes",
    "arena_capacity_bytes",
    "legacy_logical_lower_bound_bytes",
)
STORAGE_INVARIANTS = {
    "formula_clauses_equal_emitted",
    "clause_end_bytes_equal_four_per_clause",
    "arena_bytes_partition",
    "capacity_covers_logical",
    "legacy_covers_literal_payload",
    "clause_ends_monotone",
    "clause_ends_in_bounds",
    "terminal_end_matches_literals",
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


def storage_counts(value: dict[str, Any], *, label: str) -> dict[str, int]:
    return {
        name: count(value.get(name), label=f"{label}.{name}")
        for name in STORAGE_FIELDS
    }


def require_storage_accounting(
    counts: dict[str, int],
    *,
    clauses_emitted: int,
    label: str,
) -> None:
    require(
        counts["formula_clauses"] == clauses_emitted,
        f"{label} formula-clause count differs from emitted clauses",
    )
    require(
        counts["clause_end_logical_bytes"] == counts["formula_clauses"] * 4,
        f"{label} clause-end byte accounting failed",
    )
    require(
        counts["arena_logical_bytes"]
        == counts["clause_end_logical_bytes"] + counts["literal_logical_bytes"],
        f"{label} arena logical-byte accounting failed",
    )
    require(
        counts["arena_capacity_bytes"] >= counts["arena_logical_bytes"],
        f"{label} arena capacity is smaller than logical storage",
    )
    require(
        counts["legacy_logical_lower_bound_bytes"]
        >= counts["literal_logical_bytes"],
        f"{label} legacy lower bound is smaller than the literal payload",
    )
    require(
        counts["arena_logical_bytes"] * 5
        <= counts["legacy_logical_lower_bound_bytes"] * 4,
        f"{label} flat storage exceeds the frozen 80-percent gate",
    )


def instance_storage_profile(cnf: dict[str, Any], *, label: str) -> dict[str, int]:
    value = cnf.get("storage")
    require(isinstance(value, dict), f"{label} lacks flat storage profile")
    counts = storage_counts(value, label=f"{label}.storage")
    invariants = value.get("invariants")
    require(isinstance(invariants, dict), f"{label} storage lacks invariants")
    require(
        set(invariants) == STORAGE_INVARIANTS,
        f"{label} storage invariant set mismatch",
    )
    require(
        all(entry is True for entry in invariants.values()),
        f"{label} storage has a failed invariant",
    )
    require(value.get("invariants_hold") is True, f"{label} storage is invalid")
    require(
        value.get("logical_ratio_at_most_80_percent") is True,
        f"{label} storage reports a failed 80-percent gate",
    )
    require_storage_accounting(
        counts,
        clauses_emitted=count(cnf.get("clauses_emitted"), label=f"{label}.clauses_emitted"),
        label=f"{label} storage",
    )
    return counts


def summary_storage_profile(
    cnf: dict[str, Any], *, instances: int, label: str
) -> dict[str, int]:
    value = cnf.get("storage")
    require(isinstance(value, dict), f"{label} lacks flat storage profile")
    counts = storage_counts(value, label=f"{label}.storage")
    require(
        count(value.get("invariant_instances"), label=f"{label}.invariant_instances")
        == instances,
        f"{label} storage invariant population is incomplete",
    )
    require(
        count(
            value.get("logical_ratio_at_most_80_percent_instances"),
            label=f"{label}.logical_ratio_at_most_80_percent_instances",
        )
        == instances,
        f"{label} storage ratio-gate population is incomplete",
    )
    require(value.get("all_invariants_hold") is True, f"{label} storage is invalid")
    require(
        value.get("all_logical_ratios_at_most_80_percent") is True,
        f"{label} storage reports a failed 80-percent gate",
    )
    require_storage_accounting(
        counts,
        clauses_emitted=count(cnf.get("clauses_emitted"), label=f"{label}.clauses_emitted"),
        label=f"{label} storage",
    )
    return counts


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


def parity_shape(value: Any, *, label: str) -> dict[str, int]:
    require(isinstance(value, str), f"{label} parity shape is not a string")
    match = PARITY_SHAPE.fullmatch(value)
    require(match is not None, f"{label} parity shape is malformed")
    arity, false, true, distinct, repeated, complementary = map(int, match.groups())
    constants = false + true
    nonconstants = arity - constants
    pairs = arity * (arity - 1) // 2
    require(constants <= arity, f"{label} parity constants exceed arity")
    require(distinct <= nonconstants, f"{label} distinct-node count exceeds inputs")
    require(nonconstants == 0 or distinct > 0, f"{label} loses nonconstant inputs")
    require(repeated + complementary <= pairs, f"{label} parity pair count exceeds arity")
    return {
        "raw_arity": arity,
        "false_constants": false,
        "true_constants": true,
        "distinct_nonconstant_nodes": distinct,
        "repeated_literal_pairs": repeated,
        "complementary_literal_pairs": complementary,
    }


def parity_overlap_profile(
    value: Any,
    *,
    expected: dict[str, Any],
    label: str,
) -> tuple[dict[str, Any], dict[tuple[str, str, str], dict[str, Any]]]:
    require(isinstance(value, dict), f"{label} lacks parity-overlap profile")
    require(value.get("profile_complete") is True, f"{label} parity-overlap profile is incomplete")
    invariants = value.get("invariants")
    require(isinstance(invariants, dict), f"{label} parity-overlap profile lacks invariants")
    require(set(invariants) == PARITY_INVARIANTS, f"{label} parity-overlap invariant set mismatch")
    require(all(entry is True for entry in invariants.values()), f"{label} parity-overlap failed invariant")
    totals = {
        "duplicate_clauses": count(value.get("duplicate_clauses"), label=f"{label}.duplicate_clauses"),
        "duplicate_canonical_literals": count(
            value.get("duplicate_canonical_literals"),
            label=f"{label}.duplicate_canonical_literals",
        ),
        "lengths": origin_lengths(value.get("lengths"), label=label),
    }
    require(totals == expected, f"{label} parity-overlap total differs from origin subset")
    rows = value.get("rows")
    require(isinstance(rows, list), f"{label} parity-overlap rows are malformed")
    rendered: dict[tuple[str, str, str], dict[str, Any]] = {}
    summed = empty_origin_metrics()
    for index, row in enumerate(rows):
        row_label = f"{label}.parity_overlap.rows[{index}]"
        require(isinstance(row, dict), f"{row_label} is not an object")
        relation = row.get("relation")
        first_shape = row.get("first_shape")
        duplicate_shape = row.get("duplicate_shape")
        require(relation in PARITY_RELATIONS, f"{row_label} relation is invalid")
        parsed_first = parity_shape(first_shape, label=f"{row_label}.first_shape")
        parsed_duplicate = parity_shape(duplicate_shape, label=f"{row_label}.duplicate_shape")
        key = (relation, first_shape, duplicate_shape)
        require(key not in rendered, f"{row_label} repeats a parity-overlap cell")
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
            f"{row_label} parity-overlap clause partition drift",
        )
        require(
            metrics["duplicate_canonical_literals"]
            == sum(metrics["lengths"][bucket]["literals"] for bucket in LENGTH_BUCKETS),
            f"{row_label} parity-overlap literal partition drift",
        )
        rendered[key] = metrics
        add_origin_metrics(summed, metrics)
    require(summed == totals, f"{label} parity-overlap rows do not equal totals")
    return totals, rendered


def origin_profile(
    profile: dict[str, Any],
    *,
    expected_duplicate_clauses: int,
    require_parity_overlap: bool,
    label: str,
) -> tuple[
    dict[str, Any],
    dict[tuple[str, str, str], dict[str, Any]],
    dict[str, Any],
    dict[tuple[str, str, str], dict[str, Any]],
]:
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
    expected_parity = empty_origin_metrics()
    for (first, duplicate, _), metrics in rendered.items():
        if first.endswith("/and_tree/forward/parity") and duplicate.endswith(
            "/and_tree/forward/parity"
        ):
            add_origin_metrics(expected_parity, metrics)
    if require_parity_overlap:
        parity_totals, parity_rows = parity_overlap_profile(
            value.get("parity_overlap"),
            expected=expected_parity,
            label=label,
        )
    else:
        require(
            "parity_overlap" not in value,
            f"{label} legacy artifact unexpectedly carries parity-overlap data",
        )
        parity_totals = empty_origin_metrics()
        parity_rows = {}
    return totals, rendered, parity_totals, parity_rows


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
    expected_same_owner_parity_duplicates: int | None = None,
    expected_baseline_analysis: dict[str, Any] | None = None,
    require_flat_storage: bool = False,
) -> dict[str, Any]:
    artifact_version = artifact.get("version")
    require(
        artifact_version in SUPPORTED_ARTIFACT_VERSIONS,
        "artifact version mismatch",
    )
    require_parity_overlap = artifact_version >= PARITY_OVERLAP_ARTIFACT_VERSION
    if require_flat_storage:
        require(
            artifact_version >= FLAT_STORAGE_ARTIFACT_VERSION,
            "flat storage requires artifact version 38 or newer",
        )
    storage_available = artifact_version >= FLAT_STORAGE_ARTIFACT_VERSION
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
    aggregate_storage = defaultdict(int)
    families: dict[str, dict[str, Any]] = {}
    aggregate_origin_totals = empty_origin_metrics()
    aggregate_origin_rows: dict[tuple[str, str, str], dict[str, Any]] = {}
    aggregate_parity_totals = empty_origin_metrics()
    aggregate_parity_rows: dict[tuple[str, str, str], dict[str, Any]] = {}
    origin_participation: dict[tuple[str, str, str], set[int]] = defaultdict(set)
    origin_largest_instance: dict[tuple[str, str, str], int] = defaultdict(int)
    origin_families: dict[tuple[str, str, str], dict[str, dict[str, int]]] = defaultdict(
        lambda: defaultdict(lambda: {"sat": 0, "unsat": 0})
    )
    parity_participation: dict[tuple[str, str, str], set[int]] = defaultdict(set)
    parity_largest_instance: dict[tuple[str, str, str], int] = defaultdict(int)
    parity_families: dict[tuple[str, str, str], dict[str, dict[str, int]]] = defaultdict(
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
        if storage_available:
            add_counts(
                aggregate_storage,
                instance_storage_profile(cnf, label=label),
            )
        origin_totals, origin_rows, parity_totals, parity_rows = origin_profile(
            profile,
            expected_duplicate_clauses=row_counts["duplicate_clauses_skipped"],
            require_parity_overlap=require_parity_overlap,
            label=label,
        )
        add_origin_metrics(aggregate_origin_totals, origin_totals)
        add_origin_metrics(aggregate_parity_totals, parity_totals)
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
        for key, metrics in parity_rows.items():
            aggregate_row = aggregate_parity_rows.setdefault(key, empty_origin_metrics())
            add_origin_metrics(aggregate_row, metrics)
            parity_participation[key].add(index)
            parity_largest_instance[key] = max(
                parity_largest_instance[key], metrics["duplicate_clauses"]
            )
            parity_families[key][family][instance["outcome"]] += metrics[
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
    summary_storage = None
    if storage_available:
        summary_storage = summary_storage_profile(
            summary_cnf,
            instances=files,
            label="summary",
        )
        require(
            dict(aggregate_storage) == summary_storage,
            "summary storage counters do not equal per-instance sums",
        )
    (
        summary_origin_totals,
        summary_origin_rows,
        summary_parity_totals,
        summary_parity_rows,
    ) = origin_profile(
        summary_profile,
        expected_duplicate_clauses=expected_aggregate["duplicate_clauses_skipped"],
        require_parity_overlap=require_parity_overlap,
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
    require(
        aggregate_parity_totals == summary_parity_totals,
        "summary parity-overlap totals do not equal per-instance sums",
    )
    require(
        aggregate_parity_rows == summary_parity_rows,
        "summary parity-overlap rows do not equal per-instance sums",
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
    same_owner_parity_duplicates = sum(
        metrics["duplicate_clauses"]
        for (first, duplicate, relation), metrics in aggregate_origin_rows.items()
        if relation == "same"
        and first.endswith("/and_tree/forward/parity")
        and duplicate.endswith("/and_tree/forward/parity")
    )
    same_owner_parity_lengths = {
        bucket: {
            metric: sum(
                row_metrics["lengths"][bucket][metric]
                for (
                    first,
                    duplicate,
                    relation,
                ), row_metrics in aggregate_origin_rows.items()
                if relation == "same"
                and first.endswith("/and_tree/forward/parity")
                and duplicate.endswith("/and_tree/forward/parity")
            )
            for metric in ("clauses", "literals")
        }
        for bucket in LENGTH_BUCKETS
    }
    if expected_same_owner_parity_duplicates is not None:
        require(
            same_owner_parity_duplicates == expected_same_owner_parity_duplicates,
            "same-owner parity duplicate gate failed",
        )
        require(
            same_owner_parity_lengths["binary"]["clauses"]
            == expected_same_owner_parity_duplicates
            and same_owner_parity_lengths["binary"]["literals"]
            == expected_same_owner_parity_duplicates * 2
            and all(
                same_owner_parity_lengths[bucket]["clauses"] == 0
                and same_owner_parity_lengths[bucket]["literals"] == 0
                for bucket in LENGTH_BUCKETS
                if bucket != "binary"
            ),
            "same-owner parity binary partition gate failed",
        )

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
    rendered_parity_rows = []
    eligible_parity_cells = []
    all_parity_duplicates = aggregate_parity_totals["duplicate_clauses"]
    for key, metrics in sorted(aggregate_parity_rows.items()):
        clauses = metrics["duplicate_clauses"]
        participating_instances = len(parity_participation[key])
        largest_instance = parity_largest_instance[key]
        selection_eligible = (
            clauses * 2 >= all_parity_duplicates
            and participating_instances >= 10
            and largest_instance * 2 <= clauses
        )
        if selection_eligible:
            eligible_parity_cells.append(
                {
                    "relation": key[0],
                    "first_shape": key[1],
                    "duplicate_shape": key[2],
                }
            )
        rendered_parity_rows.append(
            {
                "relation": key[0],
                "first_shape_key": key[1],
                "duplicate_shape_key": key[2],
                "first_shape": parity_shape(key[1], label="aggregate first shape"),
                "duplicate_shape": parity_shape(
                    key[2], label="aggregate duplicate shape"
                ),
                **metrics,
                "participating_instances": participating_instances,
                "largest_single_instance_clauses": largest_instance,
                "largest_instance_share": (
                    largest_instance / clauses if clauses else None
                ),
                "share_of_all_parity_duplicates": (
                    clauses / all_parity_duplicates if all_parity_duplicates else None
                ),
                "selection_eligible": selection_eligible,
                "families": {
                    family: dict(outcomes)
                    for family, outcomes in sorted(parity_families[key].items())
                },
            }
        )
    report = {
        "schema": REPORT_SCHEMA,
        "accepted": True,
        "artifact": {
            "version": artifact_version,
            "corpus_hash": config.get("corpus_hash"),
            "manifest_sha256": manifest_hash,
            "config_hash": config.get("config_hash"),
        },
        "population": {"files": files, "sat": sat, "unsat": unsat},
        "aggregate": dict(aggregate),
        "storage": {
            "available": storage_available,
            **({} if summary_storage is None else summary_storage),
            "logical_ratio": (
                None
                if summary_storage is None
                or summary_storage["legacy_logical_lower_bound_bytes"] == 0
                else summary_storage["arena_logical_bytes"]
                / summary_storage["legacy_logical_lower_bound_bytes"]
            ),
            "all_invariants_hold": storage_available,
            "all_logical_ratios_at_most_80_percent": storage_available,
        },
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
            "same_owner_parity_duplicates": same_owner_parity_duplicates,
            "same_owner_parity_lengths": same_owner_parity_lengths,
            "parity_overlap": {
                "available": require_parity_overlap,
                **aggregate_parity_totals,
                "rows": rendered_parity_rows,
                "eligible_cells": eligible_parity_cells,
                "selection_rule": {
                    "minimum_share_of_all_parity_duplicates": 0.5,
                    "minimum_participating_instances": 10,
                    "maximum_largest_instance_share": 0.5,
                },
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
    if expected_baseline_analysis is not None:
        require(
            expected_baseline_analysis.get("schema")
            == "axeyum.cnf-construction-profile-analysis.v2",
            "legacy baseline analysis schema mismatch",
        )
        require(
            report["aggregate"] == expected_baseline_analysis.get("aggregate"),
            "legacy construction aggregate drift",
        )
        require(
            report["families"] == expected_baseline_analysis.get("families"),
            "legacy family aggregate drift",
        )
        baseline_origins = expected_baseline_analysis.get("duplicate_origins")
        require(isinstance(baseline_origins, dict), "legacy baseline lacks duplicate origins")
        for key in (
            "duplicate_clauses",
            "duplicate_canonical_literals",
            "lengths",
            "rows",
            "by_duplicate_origin",
            "eligible_cells",
            "selection_rule",
        ):
            require(
                report["duplicate_origins"][key] == baseline_origins.get(key),
                f"legacy duplicate-origin {key} drift",
            )
    return report


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
    parser.add_argument("--expected-same-owner-parity-duplicates", type=int)
    parser.add_argument("--expected-baseline-analysis", type=Path)
    parser.add_argument("--require-flat-storage", action="store_true")
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
        expected_same_owner_parity_duplicates=args.expected_same_owner_parity_duplicates,
        expected_baseline_analysis=(
            load_json(args.expected_baseline_analysis)
            if args.expected_baseline_analysis is not None
            else None
        ),
        require_flat_storage=args.require_flat_storage,
    )
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.out is None:
        print(rendered, end="")
    else:
        args.out.write_text(rendered, encoding="utf-8")


if __name__ == "__main__":
    main()
