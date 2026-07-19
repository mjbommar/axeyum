#!/usr/bin/env python3
"""Validate and summarize an axeyum-bench CNF construction profile."""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path
from typing import Any


ARTIFACT_VERSION = 35
REPORT_SCHEMA = "axeyum.cnf-construction-profile-analysis.v1"
INVARIANTS = {
    "non_tautological_attempts_equal_length_buckets",
    "non_tautological_attempts_equal_primary_probes",
    "occupied_probes_partition",
    "duplicates_partition",
    "emitted_partition",
    "tautologies_partition",
}
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
