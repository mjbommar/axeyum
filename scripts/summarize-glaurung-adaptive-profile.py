#!/usr/bin/env python3
"""Fail-closed summary for adaptive Glaurung profiles with native fallbacks."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import importlib.util
import json
import math
from pathlib import Path
import sys
from typing import Any


ROOT = Path(__file__).resolve().parent


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load profile validator: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


WARM = load_module("glaurung_warm_profile", ROOT / "summarize-glaurung-warm-profile.py")
NATIVE = load_module(
    "glaurung_native_profile", ROOT / "summarize-glaurung-native-profile.py"
)

SUMMARY_SCHEMA = "axeyum-glaurung-adaptive-profile-summary-v1"
CURRENT_WARM_SCHEMA = WARM.PROFILE_SCHEMAS[-1]
COMMON_PHASES = (
    "translation",
    "word_rewrite",
    "bit_blast",
    "cnf_encode",
    "solve",
    "model_lift",
    "replay",
    "model_extract",
)
PARTITION_COUNTS = (
    "assertions_added",
    "assertions_popped",
    "root_encodings",
    "aig_nodes_added",
    "cnf_variables_added",
    "cnf_clauses_added",
    *WARM.ENTRY_COUNTS_V7,
)


class ProfileError(ValueError):
    """The mixed profile cannot support a sound adaptive-policy claim."""


def nearest_rank(values: list[int], percentile: float) -> int:
    ordered = sorted(values)
    index = max(0, math.ceil(percentile * len(ordered)) - 1)
    return ordered[index]


def percentage(numerator: int, denominator: int) -> float:
    if denominator == 0:
        return 0.0
    return round(100.0 * numerator / denominator, 6)


def validate_record(row: Any, location: str) -> dict[str, Any]:
    if not isinstance(row, dict):
        raise ProfileError(f"{location}: record must be a JSON object")
    schema = row.get("schema")
    try:
        if schema == CURRENT_WARM_SCHEMA:
            return WARM.validate_record(row, location)
        if schema == NATIVE.PROFILE_SCHEMA:
            return NATIVE.validate_record(row, location)
    except (WARM.ProfileError, NATIVE.ProfileError) as error:
        raise ProfileError(str(error)) from error
    raise ProfileError(
        f"{location}: adaptive input requires {CURRENT_WARM_SCHEMA!r} or "
        f"{NATIVE.PROFILE_SCHEMA!r}, found {schema!r}"
    )


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
                    f"{location}: process {process_id} sequence must be strictly "
                    f"increasing after {previous}"
                )
            if row["schema"] == CURRENT_WARM_SCHEMA:
                path_id = row["path_id"]
                if path_id is not None:
                    path_key = (process_id, path_id)
                    first = path_key not in seen_paths
                    if row["path_created"] != first:
                        raise ProfileError(
                            f"{location}: path_created={row['path_created']} but "
                            f"first warm occurrence={first}"
                        )
                    seen_paths.add(path_key)
                elif row["path_created"]:
                    raise ProfileError(f"{location}: path_created requires a path_id")
            seen_keys.add(key)
            last_sequence[process_id] = sequence
            records.append(row)
    schemas = {row["schema"] for row in records}
    required = {CURRENT_WARM_SCHEMA, NATIVE.PROFILE_SCHEMA}
    if schemas != required:
        raise ProfileError(
            "adaptive profile must contain both current warm and native fallback "
            f"records; found {sorted(schemas)}"
        )
    return records


def normalized_phases(row: dict[str, Any]) -> dict[str, int]:
    if row["schema"] == CURRENT_WARM_SCHEMA:
        phases = {phase: row[f"{phase}_nanos"] for phase in COMMON_PHASES}
        phases["setup"] = row["session_create_nanos"]
        phases["unattributed"] = row["unattributed_nanos"]
        return phases
    phases = {phase: row[f"{phase}_nanos"] for phase in COMMON_PHASES}
    phases["setup"] = row["arena_create_nanos"] + row["solver_create_nanos"]
    attributed = sum(phases.values())
    phases["unattributed"] = row["total_nanos"] - attributed
    return phases


def latency(rows: list[dict[str, Any]]) -> dict[str, int | float | None]:
    if not rows:
        return {"total": 0, "mean": 0.0, "p50": None, "p95": None, "max": None}
    values = [row["total_nanos"] for row in rows]
    total = sum(values)
    return {
        "total": total,
        "mean": round(total / len(values), 6),
        "p50": nearest_rank(values, 0.50),
        "p95": nearest_rank(values, 0.95),
        "max": max(values),
    }


def warm_partition(rows: list[dict[str, Any]]) -> dict[str, Any]:
    phase_totals = {
        phase: sum(row[f"{phase}_nanos"] for row in rows) for phase in WARM.PHASES
    }
    return {
        "records": len(rows),
        "latency_nanos": latency(rows),
        "phases": phase_totals,
        "structure_deltas": {
            field: sum(row[field] for row in rows) for field in PARTITION_COUNTS
        },
    }


def summarize(paths: list[Path]) -> dict[str, Any]:
    records = load_records(paths)
    warm = [row for row in records if row["schema"] == CURRENT_WARM_SCHEMA]
    native = [row for row in records if row["schema"] == NATIVE.PROFILE_SCHEMA]
    total_nanos = sum(row["total_nanos"] for row in records)
    phase_totals: Counter[str] = Counter()
    for row in records:
        phase_totals.update(normalized_phases(row))
    if sum(phase_totals.values()) != total_nanos:
        raise ProfileError("normalized adaptive phases do not equal total latency")

    outcomes = Counter(row["outcome"] for row in records)
    query_counts = Counter(row["query_hash"] for row in records)
    process_rows: dict[int, list[int]] = defaultdict(list)
    for row in records:
        process_rows[row["process_id"]].append(row["sequence"])

    cache_policies = {
        (
            row["replay_sat_cache"]["enabled"],
            row["replay_sat_cache"]["max_entries"],
            row["replay_sat_cache"]["max_model_values"],
            row["replay_sat_cache"]["max_model_bits"],
        )
        for row in warm
    }
    if len(cache_policies) != 1:
        raise ProfileError("replay cache policy drift across warm profile records")
    enabled, max_entries, max_model_values, max_model_bits = cache_policies.pop()

    return {
        "schema": SUMMARY_SCHEMA,
        "profile_schemas": sorted({row["schema"] for row in records}),
        "inputs": [str(path) for path in paths],
        "records": len(records),
        "warm_records": len(warm),
        "native_fallback_records": len(native),
        "unique_queries": len(query_counts),
        "duplicate_occurrences": len(records) - len(query_counts),
        "outcomes": {outcome: outcomes[outcome] for outcome in WARM.OUTCOMES},
        "decided_percent": percentage(
            outcomes["sat"] + outcomes["unsat"], len(records)
        ),
        "latency_nanos": latency(records),
        "phases": {
            phase: {
                "nanos": phase_totals[phase],
                "percent": percentage(phase_totals[phase], total_nanos),
            }
            for phase in ("setup", *COMMON_PHASES, "unattributed")
        },
        "warm": {
            "paths_created": sum(row["path_created"] for row in warm),
            "entry_modes": {
                mode: sum(row["entry_mode"] == mode for row in warm)
                for mode in WARM.ENTRY_MODES_V7
            },
            "entry_structure_totals": {
                field: sum(row[field] for row in warm) for field in WARM.ENTRY_COUNTS_V7
            },
            "created": warm_partition([row for row in warm if row["path_created"]]),
            "retained": warm_partition(
                [row for row in warm if not row["path_created"]]
            ),
            "replay_sat_cache": {
                "enabled": bool(enabled),
                "max_entries": max_entries,
                "max_model_values": max_model_values,
                "max_model_bits": max_model_bits,
                **{
                    field: sum(row["replay_sat_cache"][field] for row in warm)
                    for field in WARM.REPLAY_SAT_CACHE_COUNTER_FIELDS
                },
                "peak_entries": max(row["replay_sat_cache"]["entries"] for row in warm),
                "peak_model_values": max(
                    row["replay_sat_cache"]["model_values"] for row in warm
                ),
                "peak_model_bits": max(
                    row["replay_sat_cache"]["model_bits"] for row in warm
                ),
            },
        },
        "native_fallbacks": {
            "timeout_ms": sorted({row["timeout_ms"] for row in native}),
            "latency_nanos": latency(native),
            "structure_totals": {
                field: sum(row[field] for row in native) for field in NATIVE.COUNTS
            },
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
    parser.add_argument(
        "profiles", nargs="+", type=Path, help="process-isolated mixed JSONL files"
    )
    parser.add_argument("--out", type=Path, help="write JSON here instead of stdout")
    parser.add_argument("--require-records", type=int)
    parser.add_argument("--require-native-fallbacks", type=int)
    parser.add_argument("--require-100-percent-decided", action="store_true")
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
        if (
            args.require_native_fallbacks is not None
            and summary["native_fallback_records"] != args.require_native_fallbacks
        ):
            raise ProfileError(
                "native fallback count is "
                f"{summary['native_fallback_records']}, expected "
                f"{args.require_native_fallbacks}"
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
