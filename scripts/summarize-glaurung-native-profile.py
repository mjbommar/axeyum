#!/usr/bin/env python3
"""Validate and summarize exact-query Glaurung native Axeyum JSONL profiles."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
import math
from pathlib import Path
import re
import sys
from typing import Any


PROFILE_SCHEMA = "glaurung-axeyum-native-profile-v1"
SUMMARY_SCHEMA = "axeyum-glaurung-native-profile-summary-v1"
QUERY_HASH = re.compile(r"sha256:[0-9a-f]{64}\Z")
OUTCOMES = ("sat", "unsat", "unknown")
PHASES = (
    "arena_create",
    "translation",
    "solver_create",
    "word_rewrite",
    "bit_blast",
    "cnf_encode",
    "solve",
    "model_lift",
    "replay",
    "model_extract",
)
COUNTS = (
    "assertion_count",
    "translated_exprs",
    "arena_terms",
    "symbols",
    "model_values",
    "root_encodings",
    "checks",
    "aig_nodes",
    "cnf_variables",
    "cnf_clauses",
)


class ProfileError(ValueError):
    """The profile stream cannot support a sound comparison."""


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
    process_id = nonnegative_int(row, "process_id", location)
    sequence = nonnegative_int(row, "sequence", location)
    query_hash = row.get("query_hash")
    if not isinstance(query_hash, str) or QUERY_HASH.fullmatch(query_hash) is None:
        raise ProfileError(f"{location}: query_hash must be sha256:<64 lowercase hex digits>")
    if row.get("word_policy") != "raw":
        raise ProfileError(f"{location}: word_policy must be 'raw' for the native control")
    timeout_ms = nonnegative_int(row, "timeout_ms", location)
    if timeout_ms == 0:
        raise ProfileError(f"{location}: timeout_ms must be positive")
    outcome = row.get("outcome")
    if outcome not in OUTCOMES:
        raise ProfileError(f"{location}: unsupported outcome {outcome!r}")
    if row.get("complete") is not True:
        raise ProfileError(f"{location}: profile is not complete")

    counts = {field: nonnegative_int(row, field, location) for field in COUNTS}
    if counts["root_encodings"] != counts["assertion_count"]:
        raise ProfileError(
            f"{location}: complete raw query encoded {counts['root_encodings']} roots "
            f"for {counts['assertion_count']} assertions"
        )
    if counts["checks"] != 1:
        raise ProfileError(f"{location}: complete one-shot query must record exactly one check")

    total = nonnegative_int(row, "total_nanos", location)
    phase_total = sum(nonnegative_int(row, f"{phase}_nanos", location) for phase in PHASES)
    if phase_total > total:
        raise ProfileError(
            f"{location}: attributed phases ({phase_total}) exceed total_nanos ({total})"
        )
    return row


def load_records(paths: list[Path]) -> list[dict[str, Any]]:
    if not paths:
        raise ProfileError("at least one JSONL profile is required")
    records: list[dict[str, Any]] = []
    last_sequence: dict[int, int] = {}
    seen_keys: set[tuple[int, int]] = set()
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
                row = json.loads(line)
            except json.JSONDecodeError as error:
                raise ProfileError(f"{location}: invalid JSON: {error}") from error
            row = validate_record(row, location)
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
            seen_keys.add(key)
            last_sequence[process_id] = sequence
            records.append(row)
    return records


def load_manifest(path: Path) -> dict[str, dict[str, Any]]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ProfileError(f"read manifest {path}: {error}") from error
    if not isinstance(payload, dict) or payload.get("version") != 1:
        raise ProfileError(f"{path}: expected corpus manifest version 1")
    if payload.get("logic") != "QF_BV" or not isinstance(payload.get("files"), list):
        raise ProfileError(f"{path}: expected QF_BV manifest with a files array")
    entries: dict[str, dict[str, Any]] = {}
    for index, entry in enumerate(payload["files"]):
        location = f"{path}:files[{index}]"
        if not isinstance(entry, dict):
            raise ProfileError(f"{location}: entry must be an object")
        query_hash = entry.get("content_hash")
        if not isinstance(query_hash, str) or QUERY_HASH.fullmatch(query_hash) is None:
            raise ProfileError(f"{location}: invalid content_hash")
        if query_hash in entries:
            raise ProfileError(f"{location}: duplicate content_hash {query_hash}")
        if entry.get("expected") not in ("sat", "unsat"):
            raise ProfileError(f"{location}: expected must be sat or unsat")
        if not isinstance(entry.get("family"), str) or not entry["family"]:
            raise ProfileError(f"{location}: family must be a non-empty string")
        entries[query_hash] = entry
    return entries


def nearest_rank(values: list[int], percentile: float) -> int:
    if not values:
        raise ProfileError("cannot compute a percentile for an empty profile")
    ordered = sorted(values)
    index = max(0, math.ceil(percentile * len(ordered)) - 1)
    return ordered[index]


def percentage(numerator: int, denominator: int) -> float:
    if denominator == 0:
        return 0.0
    return round(100.0 * numerator / denominator, 6)


def summarize(paths: list[Path], manifest_path: Path | None = None) -> dict[str, Any]:
    records = load_records(paths)
    total_nanos = sum(row["total_nanos"] for row in records)
    phase_totals = {
        phase: sum(row[f"{phase}_nanos"] for row in records) for phase in PHASES
    }
    attributed = sum(phase_totals.values())
    phase_totals["unattributed"] = total_nanos - attributed
    outcomes = Counter(row["outcome"] for row in records)
    query_counts = Counter(row["query_hash"] for row in records)

    process_rows: dict[int, list[int]] = defaultdict(list)
    for row in records:
        process_rows[row["process_id"]].append(row["sequence"])

    summary: dict[str, Any] = {
        "schema": SUMMARY_SCHEMA,
        "profile_schema": PROFILE_SCHEMA,
        "inputs": [str(path) for path in paths],
        "word_policy": "raw",
        "timeout_ms": sorted({row["timeout_ms"] for row in records}),
        "records": len(records),
        "unique_queries": len(query_counts),
        "duplicate_occurrences": len(records) - len(query_counts),
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
            phase: {
                "nanos": nanos,
                "percent": percentage(nanos, total_nanos),
            }
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

    if len(summary["timeout_ms"]) != 1:
        raise ProfileError(f"profile mixes timeout policies: {summary['timeout_ms']}")
    summary["timeout_ms"] = summary["timeout_ms"][0]

    if manifest_path is not None:
        manifest = load_manifest(manifest_path)
        family_unique: dict[str, set[str]] = defaultdict(set)
        family_occurrences: Counter[str] = Counter()
        overlap_unique: set[str] = set()
        overlap_occurrences = 0
        for row in records:
            entry = manifest.get(row["query_hash"])
            if entry is None:
                continue
            if row["outcome"] != entry["expected"]:
                raise ProfileError(
                    "manifest outcome disagreement for "
                    f"{row['query_hash']}: profile={row['outcome']} manifest={entry['expected']}"
                )
            family = entry["family"]
            overlap_unique.add(row["query_hash"])
            overlap_occurrences += 1
            family_unique[family].add(row["query_hash"])
            family_occurrences[family] += 1
        summary["manifest_overlap"] = {
            "manifest": str(manifest_path),
            "unique_queries": len(overlap_unique),
            "occurrences": overlap_occurrences,
            "families": {
                family: {
                    "unique_queries": len(family_unique[family]),
                    "occurrences": family_occurrences[family],
                }
                for family in sorted(family_unique)
            },
        }
    return summary


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profiles", nargs="+", type=Path, help="process-isolated JSONL files")
    parser.add_argument("--manifest", type=Path, help="optional Glaurung corpus manifest v1")
    parser.add_argument("--out", type=Path, help="write the JSON summary here instead of stdout")
    parser.add_argument(
        "--require-100-percent-decided",
        action="store_true",
        help="fail unless every complete record is sat or unsat",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        summary = summarize(args.profiles, args.manifest)
        if args.require_100_percent_decided and summary["decided_percent"] != 100.0:
            raise ProfileError(
                f"decided rate is {summary['decided_percent']:.3f}%, expected 100.000%"
            )
        rendered = json.dumps(summary, indent=2, sort_keys=True) + "\n"
        if args.out is None:
            sys.stdout.write(rendered)
        else:
            args.out.parent.mkdir(parents=True, exist_ok=True)
            args.out.write_text(rendered, encoding="utf-8")
    except ProfileError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
