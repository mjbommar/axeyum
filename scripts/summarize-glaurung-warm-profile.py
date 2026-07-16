#!/usr/bin/env python3
"""Fail-closed validation and summary for native Glaurung warm profiles."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
import math
from pathlib import Path
import re
import sys
from typing import Any


PROFILE_SCHEMAS = (
    "glaurung-axeyum-warm-profile-v1",
    "glaurung-axeyum-warm-profile-v2",
    "glaurung-axeyum-warm-profile-v3",
    "glaurung-axeyum-warm-profile-v4",
    "glaurung-axeyum-warm-profile-v5",
    "glaurung-axeyum-warm-profile-v6",
)
SUMMARY_SCHEMA = "axeyum-glaurung-warm-profile-summary-v1"
QUERY_HASH = re.compile(r"sha256:[0-9a-f]{64}\Z")
OUTCOMES = ("sat", "unsat", "unknown")
PHASES = (
    "session_create",
    "translation",
    "word_rewrite",
    "bit_blast",
    "cnf_encode",
    "solve",
    "model_lift",
    "replay",
    "model_extract",
    "unattributed",
)
COUNTS = (
    "assertion_count",
    "common_prefix_assertions",
    "assertions_added",
    "assertions_popped",
    "translated_exprs",
    "arena_terms",
    "symbols",
    "model_values",
    "root_encodings",
    "aig_nodes_added",
    "cnf_variables_added",
    "cnf_clauses_added",
    "aig_nodes",
    "cnf_variables",
    "cnf_clauses",
)
GATE_MIX_V2_FIELDS = (
    "and_nodes_synced",
    "up_half_definitions",
    "down_half_definitions",
    "xor_half_definitions",
    "not_ite_half_definitions",
    "not_and_half_definitions",
    "and_tree_half_definitions",
    "binary_and_half_definitions",
    "constant_clauses",
    "definition_clauses",
    "root_clauses",
    "direct_positive_and_roots",
    "direct_positive_and_nodes",
    "direct_positive_and_leaves",
    "direct_xor_leaves",
    "direct_not_ite_leaves",
    "direct_negative_and_roots",
    "fused_positive_and_roots",
    "fused_positive_and_nodes",
    "fused_xor_leaves",
    "root_assertions",
    "guarded_root_assertions",
    "repeated_same_context_roots",
    "deduplicated_root_assertions",
    "reused_cross_context_roots",
    "guarded_root_clauses",
    "root_clause_attempts",
    "unit_payload_root_clauses",
    "binary_payload_root_clauses",
    "wide_payload_root_clauses",
    "duplicate_definition_clauses",
    "duplicate_root_clauses",
    "duplicate_prior_root_clauses",
    "root_clauses_duplicate_non_root",
    "tautological_definition_clauses",
    "tautological_root_clauses",
    "fresh_negative_root_definitions",
    "reused_negative_root_definitions",
)
GATE_MIX_V3_FIELDS = GATE_MIX_V2_FIELDS + (
    "internal_positive_and_opportunities",
    "internal_positive_and_opportunity_nodes",
    "internal_positive_and_flattened",
    "internal_positive_and_immediate_clauses_avoided",
)
# The current producer schema. Kept as a public module constant for the
# focused fixture generator.
GATE_MIX_FIELDS = GATE_MIX_V3_FIELDS
AIG_CONSTRUCTION_FIELDS = (
    "and_requests",
    "and_trivial_simplifications",
    "and_absorption_simplifications",
    "and_structural_hash_hits",
    "and_nodes_created",
)
LOWERING_WORK_FIELDS = (
    "lower_calls",
    "term_memo_lookups",
    "term_memo_hits",
    "terms_lowered",
    "operand_vectors_copied",
    "operand_bits_copied",
    "root_bits_copied",
    "term_bit_bindings_written",
    "memoized_terms",
    "term_bit_bindings",
    "symbol_bit_inputs",
)
MODEL_LIFT_WORK_FIELDS = (
    "aig_recompute_nanos",
    "assignment_reconstruct_nanos",
    "model_completion_nanos",
    "aig_nodes_recomputed",
    "symbol_bit_inputs_scanned",
    "assignment_symbols_produced",
    "arena_symbols_scanned",
    "completed_model_values",
)
REPLAY_SAT_CACHE_FIELDS = (
    "enabled",
    "max_entries",
    "max_model_values",
    "max_model_bits",
    "hits",
    "misses",
    "insertions",
    "evictions",
    "replay_failures",
    "declined_unsat",
    "declined_unknown",
    "declined_oversized_models",
    "declined_non_scalar_models",
    "entries",
    "model_values",
    "model_bits",
)
REPLAY_SAT_CACHE_COUNTER_FIELDS = (
    "hits",
    "misses",
    "insertions",
    "evictions",
    "replay_failures",
    "declined_unsat",
    "declined_unknown",
    "declined_oversized_models",
    "declined_non_scalar_models",
)


def gate_mix_fields(schema: str) -> tuple[str, ...] | None:
    if schema == PROFILE_SCHEMAS[1]:
        return GATE_MIX_V2_FIELDS
    if schema in PROFILE_SCHEMAS[2:]:
        return GATE_MIX_V3_FIELDS
    return None


class ProfileError(ValueError):
    """The profile stream cannot support a sound attribution claim."""


def nonnegative_int(row: dict[str, Any], field: str, location: str) -> int:
    value = row.get(field)
    if type(value) is not int or value < 0:
        raise ProfileError(f"{location}: {field} must be a non-negative integer")
    return value


def validate_record(row: Any, location: str) -> dict[str, Any]:
    if not isinstance(row, dict):
        raise ProfileError(f"{location}: record must be a JSON object")
    if row.get("schema") not in PROFILE_SCHEMAS:
        raise ProfileError(f"{location}: unsupported schema {row.get('schema')!r}")
    nonnegative_int(row, "process_id", location)
    nonnegative_int(row, "sequence", location)
    query_hash = row.get("query_hash")
    if not isinstance(query_hash, str) or QUERY_HASH.fullmatch(query_hash) is None:
        raise ProfileError(
            f"{location}: query_hash must be sha256:<64 lowercase hex digits>"
        )
    path_id = row.get("path_id")
    if path_id is not None and (type(path_id) is not int or path_id < 0):
        raise ProfileError(
            f"{location}: path_id must be null or a non-negative integer"
        )
    if type(row.get("path_created")) is not bool:
        raise ProfileError(f"{location}: path_created must be Boolean")
    outcome = row.get("outcome")
    if outcome not in OUTCOMES:
        raise ProfileError(f"{location}: unsupported outcome {outcome!r}")
    if row.get("complete") is not True:
        raise ProfileError(f"{location}: profile is not complete")

    counts = {field: nonnegative_int(row, field, location) for field in COUNTS}
    if counts["common_prefix_assertions"] > counts["assertion_count"]:
        raise ProfileError(f"{location}: common prefix exceeds assertion count")
    if counts["assertions_added"] != counts["root_encodings"]:
        raise ProfileError(
            f"{location}: added {counts['assertions_added']} roots but encoded "
            f"{counts['root_encodings']}"
        )
    for added, retained in (
        ("aig_nodes_added", "aig_nodes"),
        ("cnf_variables_added", "cnf_variables"),
        ("cnf_clauses_added", "cnf_clauses"),
    ):
        if counts[added] > counts[retained]:
            raise ProfileError(f"{location}: {added} exceeds current {retained}")

    total = nonnegative_int(row, "total_nanos", location)
    phase_total = sum(
        nonnegative_int(row, f"{phase}_nanos", location) for phase in PHASES
    )
    if phase_total != total:
        raise ProfileError(
            f"{location}: phases including unattributed ({phase_total}) "
            f"do not equal total_nanos ({total})"
        )
    expected_gate_fields = gate_mix_fields(row["schema"])
    if expected_gate_fields is not None:
        gate_mix = row.get("cnf_gate_mix")
        if not isinstance(gate_mix, dict) or set(gate_mix) != set(expected_gate_fields):
            raise ProfileError(f"{location}: cnf_gate_mix has an incomplete field set")
        for field in expected_gate_fields:
            nonnegative_int(gate_mix, field, f"{location}:cnf_gate_mix")
        halves = gate_mix["up_half_definitions"] + gate_mix["down_half_definitions"]
        shapes = sum(
            gate_mix[field]
            for field in (
                "xor_half_definitions",
                "not_ite_half_definitions",
                "not_and_half_definitions",
                "and_tree_half_definitions",
                "binary_and_half_definitions",
            )
        )
        if halves != shapes:
            raise ProfileError(
                f"{location}: CNF half-definition shape partition mismatch"
            )
        for fused, direct in (
            ("fused_positive_and_roots", "direct_positive_and_roots"),
            ("fused_positive_and_nodes", "direct_positive_and_nodes"),
            ("fused_xor_leaves", "direct_xor_leaves"),
            ("deduplicated_root_assertions", "repeated_same_context_roots"),
        ):
            if gate_mix[fused] > gate_mix[direct]:
                raise ProfileError(f"{location}: {fused} exceeds {direct}")
        if row["schema"] in PROFILE_SCHEMAS[2:]:
            opportunities = gate_mix["internal_positive_and_opportunities"]
            opportunity_nodes = gate_mix["internal_positive_and_opportunity_nodes"]
            flattened = gate_mix["internal_positive_and_flattened"]
            clauses_avoided = gate_mix[
                "internal_positive_and_immediate_clauses_avoided"
            ]
            if opportunity_nodes < 2 * opportunities:
                raise ProfileError(
                    f"{location}: internal AND opportunity nodes are incomplete"
                )
            if flattened > opportunities:
                raise ProfileError(
                    f"{location}: internal AND applications exceed opportunities"
                )
            if clauses_avoided < flattened or (flattened == 0 and clauses_avoided != 0):
                raise ProfileError(
                    f"{location}: internal AND immediate clause avoidance does not match applications"
                )
    if row["schema"] in PROFILE_SCHEMAS[3:]:
        aig = row.get("aig_construction")
        if not isinstance(aig, dict) or set(aig) != set(AIG_CONSTRUCTION_FIELDS):
            raise ProfileError(
                f"{location}: aig_construction has an incomplete field set"
            )
        for field in AIG_CONSTRUCTION_FIELDS:
            nonnegative_int(aig, field, f"{location}:aig_construction")
        classified = sum(
            aig[field]
            for field in (
                "and_trivial_simplifications",
                "and_absorption_simplifications",
                "and_structural_hash_hits",
                "and_nodes_created",
            )
        )
        if aig["and_requests"] != classified:
            raise ProfileError(f"{location}: AIG AND request partition mismatch")

        work = row.get("lowering_work")
        if not isinstance(work, dict) or set(work) != set(LOWERING_WORK_FIELDS):
            raise ProfileError(f"{location}: lowering_work has an incomplete field set")
        for field in LOWERING_WORK_FIELDS:
            nonnegative_int(work, field, f"{location}:lowering_work")
        if work["term_memo_hits"] > work["term_memo_lookups"]:
            raise ProfileError(f"{location}: term memo hits exceed lookups")
        if work["terms_lowered"] != work["memoized_terms"]:
            raise ProfileError(
                f"{location}: newly lowered and retained term counts differ"
            )
        if work["term_bit_bindings_written"] != work["term_bit_bindings"]:
            raise ProfileError(f"{location}: term-bit write and retained deltas differ")
        if (
            aig["and_nodes_created"] + work["symbol_bit_inputs"]
            != counts["aig_nodes_added"]
        ):
            raise ProfileError(f"{location}: AIG node allocation partition mismatch")
    if row["schema"] in PROFILE_SCHEMAS[4:]:
        cache = row.get("replay_sat_cache")
        if not isinstance(cache, dict) or set(cache) != set(REPLAY_SAT_CACHE_FIELDS):
            raise ProfileError(
                f"{location}: replay_sat_cache has an incomplete field set"
            )
        for field in REPLAY_SAT_CACHE_FIELDS:
            nonnegative_int(cache, field, f"{location}:replay_sat_cache")
        if cache["enabled"] not in (0, 1):
            raise ProfileError(f"{location}: replay cache enabled must be zero or one")
        policy_fields = ("max_entries", "max_model_values", "max_model_bits")
        gauges = ("entries", "model_values", "model_bits")
        if cache["enabled"] == 0:
            if any(
                cache[field] for field in REPLAY_SAT_CACHE_FIELDS if field != "enabled"
            ):
                raise ProfileError(
                    f"{location}: disabled replay cache has nonzero state"
                )
        else:
            if any(cache[field] == 0 for field in policy_fields):
                raise ProfileError(f"{location}: enabled replay cache has a zero bound")
            attempts = cache["hits"] + cache["misses"] + cache["replay_failures"]
            if attempts != 1:
                raise ProfileError(
                    f"{location}: replay cache hit/miss partition is not one check"
                )
            if cache["hits"] and outcome != "sat":
                raise ProfileError(f"{location}: replay cache hit is not SAT")
            declined = sum(
                cache[field]
                for field in (
                    "declined_unsat",
                    "declined_unknown",
                    "declined_oversized_models",
                    "declined_non_scalar_models",
                )
            )
            if cache["misses"] != cache["insertions"] + declined:
                raise ProfileError(
                    f"{location}: replay cache fresh-result partition mismatch"
                )
            for gauge, bound in zip(gauges, policy_fields, strict=True):
                if cache[gauge] > cache[bound]:
                    raise ProfileError(
                        f"{location}: replay cache {gauge} exceeds {bound}"
                    )
    if row["schema"] == PROFILE_SCHEMAS[5]:
        work = row.get("model_lift_work")
        if not isinstance(work, dict) or set(work) != set(MODEL_LIFT_WORK_FIELDS):
            raise ProfileError(
                f"{location}: model_lift_work has an incomplete field set"
            )
        for field in MODEL_LIFT_WORK_FIELDS:
            nonnegative_int(work, field, f"{location}:model_lift_work")
        nested_nanos = sum(
            work[field]
            for field in (
                "aig_recompute_nanos",
                "assignment_reconstruct_nanos",
                "model_completion_nanos",
            )
        )
        if nested_nanos > row["model_lift_nanos"]:
            raise ProfileError(
                f"{location}: model-lift subphases exceed model_lift_nanos"
            )
        if work["symbol_bit_inputs_scanned"] > work["aig_nodes_recomputed"]:
            raise ProfileError(
                f"{location}: model-lift symbol bits exceed recomputed AIG nodes"
            )
        if work["assignment_symbols_produced"] > work["arena_symbols_scanned"]:
            raise ProfileError(
                f"{location}: reconstructed symbols exceed scanned arena symbols"
            )
        if work["completed_model_values"] > work["arena_symbols_scanned"]:
            raise ProfileError(
                f"{location}: completed values exceed scanned arena symbols"
            )
    return row


def load_records(paths: list[Path]) -> list[dict[str, Any]]:
    if not paths:
        raise ProfileError("at least one JSONL profile is required")
    records: list[dict[str, Any]] = []
    last_sequence: dict[int, int] = {}
    seen_keys: set[tuple[int, int]] = set()
    seen_paths: set[tuple[int, int]] = set()
    for path in paths:
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except OSError as error:
            raise ProfileError(f"read {path}: {error}") from error
        if not lines:
            raise ProfileError(f"{path}: profile is empty")
        for line_number, line in enumerate(lines, start=1):
            location = f"{path}:{line_number}"
            if not line.strip():
                raise ProfileError(f"{location}: blank JSONL record")
            try:
                row = validate_record(json.loads(line), location)
            except json.JSONDecodeError as error:
                raise ProfileError(f"{location}: invalid JSON: {error}") from error
            process_id = row["process_id"]
            sequence = row["sequence"]
            key = (process_id, sequence)
            if key in seen_keys:
                raise ProfileError(f"{location}: duplicate process/sequence key {key}")
            previous = last_sequence.get(process_id)
            if previous is not None and sequence <= previous:
                raise ProfileError(
                    f"{location}: process {process_id} sequence must be strictly increasing "
                    f"after {previous}"
                )
            path_id = row["path_id"]
            if path_id is not None:
                path_key = (process_id, path_id)
                first = path_key not in seen_paths
                if row["path_created"] != first:
                    raise ProfileError(
                        f"{location}: path_created={row['path_created']} but first occurrence={first}"
                    )
                seen_paths.add(path_key)
            elif row["path_created"]:
                raise ProfileError(f"{location}: path_created requires a path_id")
            seen_keys.add(key)
            last_sequence[process_id] = sequence
            records.append(row)
    return records


def nearest_rank(values: list[int], percentile: float) -> int:
    ordered = sorted(values)
    index = max(0, math.ceil(percentile * len(ordered)) - 1)
    return ordered[index]


def percentage(numerator: int, denominator: int) -> float:
    if denominator == 0:
        return 0.0
    return round(100.0 * numerator / denominator, 6)


def summarize(paths: list[Path]) -> dict[str, Any]:
    records = load_records(paths)
    total_nanos = sum(row["total_nanos"] for row in records)
    phase_totals = {
        phase: sum(row[f"{phase}_nanos"] for row in records) for phase in PHASES
    }
    outcomes = Counter(row["outcome"] for row in records)
    query_counts = Counter(row["query_hash"] for row in records)
    process_rows: dict[int, list[int]] = defaultdict(list)
    for row in records:
        process_rows[row["process_id"]].append(row["sequence"])

    schemas = sorted({row["schema"] for row in records})
    summary = {
        "schema": SUMMARY_SCHEMA,
        "profile_schemas": schemas,
        "inputs": [str(path) for path in paths],
        "records": len(records),
        "unique_queries": len(query_counts),
        "duplicate_occurrences": len(records) - len(query_counts),
        "paths_created": sum(1 for row in records if row["path_created"]),
        "outcomes": {outcome: outcomes[outcome] for outcome in OUTCOMES},
        "decided_percent": percentage(
            outcomes["sat"] + outcomes["unsat"], len(records)
        ),
        "latency_nanos": {
            "total": total_nanos,
            "mean": round(total_nanos / len(records), 6),
            "p50": nearest_rank([row["total_nanos"] for row in records], 0.50),
            "p95": nearest_rank([row["total_nanos"] for row in records], 0.95),
            "max": max(row["total_nanos"] for row in records),
        },
        "phases": {
            phase: {"nanos": nanos, "percent": percentage(nanos, total_nanos)}
            for phase, nanos in phase_totals.items()
        },
        "structure_totals": {
            field: sum(row[field] for row in records) for field in COUNTS
        },
        "processes": [
            {
                "process_id": process_id,
                "first_sequence": sequences[0],
                "last_sequence": sequences[-1],
                "records": len(sequences),
            }
            for process_id, sequences in sorted(process_rows.items())
        ],
    }
    homogeneous_gate_fields = gate_mix_fields(schemas[0]) if len(schemas) == 1 else None
    if homogeneous_gate_fields is not None:
        summary["cnf_gate_mix_totals"] = {
            field: sum(row["cnf_gate_mix"][field] for row in records)
            for field in homogeneous_gate_fields
        }
    if len(schemas) == 1 and schemas[0] in PROFILE_SCHEMAS[3:]:
        summary["aig_construction_totals"] = {
            field: sum(row["aig_construction"][field] for row in records)
            for field in AIG_CONSTRUCTION_FIELDS
        }
        summary["lowering_work_totals"] = {
            field: sum(row["lowering_work"][field] for row in records)
            for field in LOWERING_WORK_FIELDS
        }
    if len(schemas) == 1 and schemas[0] == PROFILE_SCHEMAS[5]:
        summary["model_lift_work_totals"] = {
            field: sum(row["model_lift_work"][field] for row in records)
            for field in MODEL_LIFT_WORK_FIELDS
        }
    if len(schemas) == 1 and schemas[0] in PROFILE_SCHEMAS[4:]:
        policies = {
            (
                row["replay_sat_cache"]["enabled"],
                row["replay_sat_cache"]["max_entries"],
                row["replay_sat_cache"]["max_model_values"],
                row["replay_sat_cache"]["max_model_bits"],
            )
            for row in records
        }
        if len(policies) != 1:
            raise ProfileError("replay cache policy drift across profile records")
        enabled, max_entries, max_model_values, max_model_bits = policies.pop()
        cache_summary = {
            "enabled": bool(enabled),
            "max_entries": max_entries,
            "max_model_values": max_model_values,
            "max_model_bits": max_model_bits,
            **{
                field: sum(row["replay_sat_cache"][field] for row in records)
                for field in REPLAY_SAT_CACHE_COUNTER_FIELDS
            },
            "peak_entries": max(row["replay_sat_cache"]["entries"] for row in records),
            "peak_model_values": max(
                row["replay_sat_cache"]["model_values"] for row in records
            ),
            "peak_model_bits": max(
                row["replay_sat_cache"]["model_bits"] for row in records
            ),
        }
        summary["replay_sat_cache"] = cache_summary
    return summary


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "profiles", nargs="+", type=Path, help="process-isolated JSONL files"
    )
    parser.add_argument(
        "--out", type=Path, help="write the JSON summary here instead of stdout"
    )
    parser.add_argument(
        "--require-records", type=int, help="fail unless this many records exist"
    )
    parser.add_argument(
        "--require-100-percent-decided",
        action="store_true",
        help="fail unless every complete record is sat or unsat",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        summary = summarize(args.profiles)
        if (
            args.require_records is not None
            and summary["records"] != args.require_records
        ):
            raise ProfileError(
                f"record count is {summary['records']}, expected {args.require_records}"
            )
        if args.require_100_percent_decided and summary["decided_percent"] != 100.0:
            raise ProfileError(
                f"decided rate is {summary['decided_percent']:.3f}%, expected 100%"
            )
    except ProfileError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    rendered = json.dumps(summary, indent=2, sort_keys=True) + "\n"
    if args.out is None:
        sys.stdout.write(rendered)
    else:
        try:
            args.out.write_text(rendered, encoding="utf-8")
        except OSError as error:
            print(f"error: write {args.out}: {error}", file=sys.stderr)
            return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
