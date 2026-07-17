#!/usr/bin/env python3
"""Join one ordered four-cell trace to cold/warm Axeyum phase profiles.

Profile clocks and JSON emission are diagnostic overhead, so this tool reports
internal phase/work attribution only. Publication speed ratios continue to
come from the unprofiled N>=5 four-cell reports.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import pathlib
import sys
from collections import Counter
from typing import Any, Iterable, Sequence


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
PAIRED_SCRIPT = SCRIPT_DIR / "analyze-glaurung-paired-traces.py"
PAIRED_SPEC = importlib.util.spec_from_file_location("glaurung_paired_profile", PAIRED_SCRIPT)
assert PAIRED_SPEC is not None and PAIRED_SPEC.loader is not None
paired = importlib.util.module_from_spec(PAIRED_SPEC)
sys.modules[PAIRED_SPEC.name] = paired
PAIRED_SPEC.loader.exec_module(paired)

SCHEMA = "axeyum-glaurung-profiled-trace-analysis-v1"
COLD_SCHEMA = "glaurung-axeyum-native-profile-v1"
WARM_SCHEMA = "glaurung-axeyum-warm-profile-v7"
COLD_PHASES = (
    "arena_create_nanos",
    "translation_nanos",
    "solver_create_nanos",
    "word_rewrite_nanos",
    "bit_blast_nanos",
    "cnf_encode_nanos",
    "solve_nanos",
    "model_lift_nanos",
    "replay_nanos",
    "model_extract_nanos",
)
WARM_PHASES = (
    "session_create_nanos",
    "translation_nanos",
    "word_rewrite_nanos",
    "bit_blast_nanos",
    "cnf_encode_nanos",
    "solve_nanos",
    "model_lift_nanos",
    "replay_nanos",
    "model_extract_nanos",
)


def fail(message: str) -> None:
    raise paired.AnalysisError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require_nonnegative_int(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        fail(f"{label} is not a nonnegative integer")
    return value


def load_profiles(path: pathlib.Path) -> tuple[list[dict[str, Any]], bytes]:
    try:
        data = path.read_bytes()
    except OSError as error:
        fail(f"cannot read {path}: {error}")
    records: list[dict[str, Any]] = []
    for line_number, line in enumerate(data.splitlines(), 1):
        if not line.strip():
            fail(f"blank profile line {line_number} in {path}")
        try:
            record = json.loads(line)
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            fail(f"invalid profile line {line_number} in {path}: {error}")
        if not isinstance(record, dict):
            fail(f"profile line {line_number} in {path} is not an object")
        if record.get("sequence") != len(records):
            fail(f"profile sequence gap at line {line_number} in {path}")
        records.append(record)
    if not records:
        fail(f"profile stream is empty: {path}")
    return records, data


def outcome_name(outcome: Any) -> str:
    return outcome.value if hasattr(outcome, "value") else str(outcome).lower()


def validate_profile_record(record: dict[str, Any], schema: str, check: Any) -> None:
    if record.get("schema") != schema:
        fail(f"missing {schema} record for {check.check_id}")
    if record.get("query_hash") != f"sha256:{check.query_sha256}":
        fail(f"profile/query hash mismatch for {check.check_id}")
    expected_outcome = (
        check.axeyum_cold_outcome if schema == COLD_SCHEMA else check.axeyum_warm_outcome
    )
    if record.get("outcome") != outcome_name(expected_outcome):
        fail(f"profile outcome mismatch for {check.check_id}")
    if record.get("complete") is not True:
        fail(f"incomplete profile for {check.check_id}")


def phase_values(
    record: dict[str, Any], phases: Sequence[str], label: str
) -> tuple[dict[str, int], int]:
    values = {
        phase: require_nonnegative_int(record.get(phase), f"{label} {phase}")
        for phase in phases
    }
    total = require_nonnegative_int(record.get("total_nanos"), f"{label} total_nanos")
    attributed = sum(values.values())
    if attributed > total:
        fail(f"{label} attributed phases exceed total")
    return values, total - attributed


def join_trace_profiles(trace: Any, records: Sequence[dict[str, Any]]) -> list[dict[str, Any]]:
    if trace.measurement_schema != paired.MEASUREMENT_SCHEMA_V2:
        fail("profile join requires a four-cell v2 trace")
    if len(records) != 2 * len(trace.checks):
        fail(
            f"profile/check cardinality mismatch: {len(records)} records for "
            f"{len(trace.checks)} checks"
        )
    query_counts = Counter(check.query_sha256 for check in trace.checks)
    rows: list[dict[str, Any]] = []
    for index, check in enumerate(trace.checks):
        pair = records[2 * index : 2 * index + 2]
        schemas = {record.get("schema") for record in pair}
        if schemas != {COLD_SCHEMA, WARM_SCHEMA}:
            fail(f"profile pair schema mismatch for {check.check_id}")
        cold = next(record for record in pair if record["schema"] == COLD_SCHEMA)
        warm = next(record for record in pair if record["schema"] == WARM_SCHEMA)
        validate_profile_record(cold, COLD_SCHEMA, check)
        validate_profile_record(warm, WARM_SCHEMA, check)
        cold_phases, cold_unattributed = phase_values(cold, COLD_PHASES, "cold")
        warm_phases, warm_unattributed = phase_values(warm, WARM_PHASES, "warm")
        declared_unattributed = require_nonnegative_int(
            warm.get("unattributed_nanos"), "warm unattributed_nanos"
        )
        if declared_unattributed != warm_unattributed:
            fail(f"warm unattributed timing mismatch for {check.check_id}")
        row: dict[str, Any] = {
            "driver": trace.driver_label,
            "driver_sha256": trace.driver_sha256,
            "index": index,
            "check_id": check.check_id,
            "query_sha256": check.query_sha256,
            "purpose": check.purpose,
            "outcome": cold["outcome"],
            "warm_execution": check.axeyum_warm_execution,
            "active_constraint_count": check.active_constraint_count,
            "query_occurrences_per_run": query_counts[check.query_sha256],
            "cold_total_nanos": cold["total_nanos"],
            "cold_unattributed_nanos": cold_unattributed,
            "warm_total_nanos": warm["total_nanos"],
            "warm_unattributed_nanos": warm_unattributed,
            "cold_aig_nodes": require_nonnegative_int(cold.get("aig_nodes"), "cold AIG nodes"),
            "cold_cnf_variables": require_nonnegative_int(
                cold.get("cnf_variables"), "cold CNF variables"
            ),
            "cold_cnf_clauses": require_nonnegative_int(
                cold.get("cnf_clauses"), "cold CNF clauses"
            ),
            "warm_aig_nodes_added": require_nonnegative_int(
                warm.get("aig_nodes_added"), "warm AIG nodes added"
            ),
            "warm_cnf_variables_added": require_nonnegative_int(
                warm.get("cnf_variables_added"), "warm CNF variables added"
            ),
            "warm_cnf_clauses_added": require_nonnegative_int(
                warm.get("cnf_clauses_added"), "warm CNF clauses added"
            ),
        }
        row.update({f"cold_{name}": value for name, value in cold_phases.items()})
        row.update({f"warm_{name}": value for name, value in warm_phases.items()})
        rows.append(row)
    return rows


def aggregate_cell(rows: Sequence[dict[str, Any]], cell: str) -> dict[str, Any]:
    phases = COLD_PHASES if cell == "cold" else WARM_PHASES
    phase_totals = {
        phase.removesuffix("_nanos"): sum(row[f"{cell}_{phase}"] for row in rows)
        for phase in phases
    }
    unattributed = sum(row[f"{cell}_unattributed_nanos"] for row in rows)
    adapter_total = sum(row[f"{cell}_total_nanos"] for row in rows)
    attributed = sum(phase_totals.values())
    if attributed + unattributed != adapter_total:
        fail(f"{cell} aggregate timing identity mismatch")
    return {
        "occurrences": len(rows),
        "adapter_total_nanos": adapter_total,
        "attributed_nanos": attributed,
        "unattributed_nanos": unattributed,
        "phase_nanos": phase_totals,
        "phase_share_of_adapter_total": {
            phase: value / adapter_total if adapter_total else None
            for phase, value in phase_totals.items()
        },
        "unattributed_share_of_adapter_total": (
            unattributed / adapter_total if adapter_total else None
        ),
    }


def aggregate(rows: Sequence[dict[str, Any]]) -> dict[str, Any]:
    return {
        "occurrences": len(rows),
        "cold": aggregate_cell(rows, "cold"),
        "warm": aggregate_cell(rows, "warm"),
        "structure": {
            "cold_aig_nodes_sum": sum(row["cold_aig_nodes"] for row in rows),
            "cold_cnf_variables_sum": sum(row["cold_cnf_variables"] for row in rows),
            "cold_cnf_clauses_sum": sum(row["cold_cnf_clauses"] for row in rows),
            "warm_aig_nodes_added": sum(row["warm_aig_nodes_added"] for row in rows),
            "warm_cnf_variables_added": sum(
                row["warm_cnf_variables_added"] for row in rows
            ),
            "warm_cnf_clauses_added": sum(row["warm_cnf_clauses_added"] for row in rows),
        },
    }


def grouped(rows: Sequence[dict[str, Any]], key: str) -> dict[str, Any]:
    groups: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        groups.setdefault(str(row[key]), []).append(row)
    return {name: aggregate(group) for name, group in sorted(groups.items())}


def analyze(
    trace_path: pathlib.Path, profile_path: pathlib.Path
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    manifest = paired.load_json(trace_path / "trace-manifest-v1.json")
    if not isinstance(manifest, dict) or manifest.get("worker_count") != 1:
        fail("ordered profile joining requires exactly one trace worker")
    trace = paired.load_trace(trace_path)
    records, profile_bytes = load_profiles(profile_path)
    process_id = manifest.get("process_id")
    if not isinstance(process_id, str) or not process_id.startswith("process-"):
        fail("trace manifest has no canonical process ID")
    try:
        expected_profile_process = int(process_id.removeprefix("process-"))
    except ValueError:
        fail("trace manifest process ID is not numeric")
    if any(record.get("process_id") != expected_profile_process for record in records):
        fail("profile process ID does not match the ordered trace")
    rows = join_trace_profiles(trace, records)
    report = {
        "schema": SCHEMA,
        "trace": {"path": str(trace_path), "driver": trace.driver_label},
        "profile": {"path": str(profile_path), "sha256": sha256(profile_bytes)},
        "methodology": {
            "unit": "one ordered four-cell check occurrence",
            "join": "exact check order plus query hash, one cold and one warm profile",
            "timing_use": "diagnostic phase attribution only; profiling overhead invalidates headline ratios",
            "timing_identity": "named nonoverlapping phases plus unattributed equals adapter total",
        },
        "overall": aggregate(rows),
        "by_outcome": grouped(rows, "outcome"),
        "by_purpose": grouped(rows, "purpose"),
        "by_warm_execution": grouped(rows, "warm_execution"),
    }
    return report, rows


def write_csv(rows: Iterable[dict[str, Any]], path: pathlib.Path) -> None:
    rows = list(rows)
    if not rows:
        fail("cannot write an empty profile join")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as output:
        writer = csv.DictWriter(output, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("trace", type=pathlib.Path)
    parser.add_argument("profile", type=pathlib.Path)
    parser.add_argument("--output", type=pathlib.Path)
    parser.add_argument("--rows-csv", type=pathlib.Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        report, rows = analyze(args.trace, args.profile)
        if args.rows_csv is not None:
            write_csv(rows, args.rows_csv)
        rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.output is None:
            sys.stdout.write(rendered)
        else:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(rendered, encoding="utf-8")
    except paired.AnalysisError as error:
        print(f"profiled trace analysis failed: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
