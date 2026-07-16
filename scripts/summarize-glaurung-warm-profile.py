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


PROFILE_SCHEMA = "glaurung-axeyum-warm-profile-v1"
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
    if row.get("schema") != PROFILE_SCHEMA:
        raise ProfileError(f"{location}: unsupported schema {row.get('schema')!r}")
    nonnegative_int(row, "process_id", location)
    nonnegative_int(row, "sequence", location)
    query_hash = row.get("query_hash")
    if not isinstance(query_hash, str) or QUERY_HASH.fullmatch(query_hash) is None:
        raise ProfileError(f"{location}: query_hash must be sha256:<64 lowercase hex digits>")
    path_id = row.get("path_id")
    if path_id is not None and (type(path_id) is not int or path_id < 0):
        raise ProfileError(f"{location}: path_id must be null or a non-negative integer")
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
    phase_total = sum(nonnegative_int(row, f"{phase}_nanos", location) for phase in PHASES)
    if phase_total != total:
        raise ProfileError(
            f"{location}: phases including unattributed ({phase_total}) "
            f"do not equal total_nanos ({total})"
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

    return {
        "schema": SUMMARY_SCHEMA,
        "profile_schema": PROFILE_SCHEMA,
        "inputs": [str(path) for path in paths],
        "records": len(records),
        "unique_queries": len(query_counts),
        "duplicate_occurrences": len(records) - len(query_counts),
        "paths_created": sum(1 for row in records if row["path_created"]),
        "outcomes": {outcome: outcomes[outcome] for outcome in OUTCOMES},
        "decided_percent": percentage(outcomes["sat"] + outcomes["unsat"], len(records)),
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


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profiles", nargs="+", type=Path, help="process-isolated JSONL files")
    parser.add_argument("--out", type=Path, help="write the JSON summary here instead of stdout")
    parser.add_argument("--require-records", type=int, help="fail unless this many records exist")
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
        if args.require_records is not None and summary["records"] != args.require_records:
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
