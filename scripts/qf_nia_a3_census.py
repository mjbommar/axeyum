#!/usr/bin/env python3
"""Validate and extract the exact retained QF_NIA A3 residual population."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import pathlib
import sys
from collections import Counter


class CensusError(ValueError):
    """The retained population or its sidecar does not satisfy the contract."""


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_population(path: pathlib.Path) -> list[str]:
    entries = [line.strip() for line in path.read_text(encoding="utf-8").splitlines()]
    entries = [entry for entry in entries if entry]
    if not entries:
        raise CensusError(f"population is empty: {path}")
    if len(entries) != len(set(entries)):
        raise CensusError(f"population contains duplicate exact paths: {path}")
    missing = [entry for entry in entries if not pathlib.Path(entry).is_file()]
    if missing:
        raise CensusError(f"population path is missing: {missing[0]}")
    basenames = [pathlib.Path(entry).name for entry in entries]
    duplicate_basenames = sorted(name for name, count in Counter(basenames).items() if count > 1)
    if duplicate_basenames:
        raise CensusError(
            "population cannot bind a basename sidecar uniquely: " + duplicate_basenames[0]
        )
    return entries


def read_sidecar(path: pathlib.Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as source:
        reader = csv.DictReader(source, delimiter="\t")
        expected = ["file", "axeyum", "reference", "declared"]
        if reader.fieldnames != expected:
            raise CensusError(f"unexpected sidecar columns in {path}: {reader.fieldnames}")
        rows = list(reader)
    names = [row["file"] for row in rows]
    if len(names) != len(set(names)):
        raise CensusError(f"sidecar contains duplicate file rows: {path}")
    allowed = {"sat", "unsat", "unsolved"}
    for row in rows:
        for field in ("axeyum", "reference"):
            if row[field] not in allowed:
                raise CensusError(f"invalid {field} status for {row['file']}: {row[field]}")
    return rows


def extract(
    population_path: pathlib.Path,
    sidecar_path: pathlib.Path,
    *,
    expected_population_sha256: str,
    expected_sidecar_sha256: str,
    expected_rows: int,
    expected_reference_only: int,
) -> tuple[list[str], dict[str, object]]:
    population_sha256 = sha256_file(population_path)
    sidecar_sha256 = sha256_file(sidecar_path)
    if population_sha256 != expected_population_sha256:
        raise CensusError(
            f"population SHA-256 differs: {population_sha256} != {expected_population_sha256}"
        )
    if sidecar_sha256 != expected_sidecar_sha256:
        raise CensusError(
            f"sidecar SHA-256 differs: {sidecar_sha256} != {expected_sidecar_sha256}"
        )

    population = read_population(population_path)
    rows = read_sidecar(sidecar_path)
    if len(population) != expected_rows or len(rows) != expected_rows:
        raise CensusError(
            f"expected {expected_rows} population/sidecar rows, got {len(population)}/{len(rows)}"
        )
    by_basename = {pathlib.Path(entry).name: entry for entry in population}
    sidecar_names = {row["file"] for row in rows}
    if sidecar_names != set(by_basename):
        missing = sorted(set(by_basename) - sidecar_names)
        extra = sorted(sidecar_names - set(by_basename))
        raise CensusError(f"sidecar population drift: missing={missing[:1]} extra={extra[:1]}")

    status_counts = Counter((row["axeyum"], row["reference"]) for row in rows)
    reference_only_names = {
        row["file"]
        for row in rows
        if row["axeyum"] == "unsolved" and row["reference"] in {"sat", "unsat"}
    }
    residual = [entry for entry in population if pathlib.Path(entry).name in reference_only_names]
    if len(residual) != expected_reference_only:
        raise CensusError(
            f"expected {expected_reference_only} reference-only rows, got {len(residual)}"
        )

    summary: dict[str, object] = {
        "schema": "axeyum-qf-nia-a3-extraction-v1",
        "population_path": str(population_path),
        "population_sha256": population_sha256,
        "sidecar_path": str(sidecar_path),
        "sidecar_sha256": sidecar_sha256,
        "population_rows": len(population),
        "status_counts": {
            f"{axeyum}/{reference}": count
            for (axeyum, reference), count in sorted(status_counts.items())
        },
        "reference_only_rows": len(residual),
    }
    return residual, summary


def first_causal_decline(trace: dict[str, object]) -> dict[str, str]:
    attempts = trace.get("attempts")
    if not isinstance(attempts, list):
        raise CensusError("trace has no attempts array")
    for attempt in attempts:
        if not isinstance(attempt, dict) or attempt.get("outcome") != "declined":
            continue
        reason = attempt.get("reason")
        if reason in {"not-applicable", "unsupported"}:
            continue
        route = attempt.get("route")
        if not isinstance(route, str) or not isinstance(reason, str):
            raise CensusError("declined trace attempt lacks a string route/reason")
        result = {"route": route, "reason": reason}
        for field in ("kind", "detail"):
            value = attempt.get(field)
            if isinstance(value, str):
                result[field] = value
        return result
    return {"route": "none", "reason": "no-causal-decline"}


def analyze_traces(residual: list[str], trace_path: pathlib.Path) -> dict[str, object]:
    records = []
    for line_number, line in enumerate(
        trace_path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError as error:
            raise CensusError(f"invalid trace JSON at {trace_path}:{line_number}: {error}") from error
        if not isinstance(record, dict):
            raise CensusError(f"trace row is not an object at {trace_path}:{line_number}")
        records.append(record)
    identities = [record.get("file") for record in records]
    if identities != residual:
        raise CensusError(
            f"trace identity/order differs: expected {len(residual)} rows, got {len(records)}"
        )

    buckets: Counter[tuple[str, str, str]] = Counter()
    cases = []
    for record in records:
        status = record.get("status")
        trace: dict[str, object] | None
        if status == "decided" and isinstance(record.get("trace"), dict):
            trace = record["trace"]
            if trace.get("schema_version") != 1:
                raise CensusError(f"unsupported trace schema for {record['file']}")
            decline = first_causal_decline(trace)
        elif status == "ingest-resource-limit":
            detail = record.get("detail")
            if record.get("verdict") != "unknown" or not isinstance(detail, str) or not detail:
                raise CensusError(
                    f"invalid ingest resource-limit record for {record.get('file')}"
                )
            if "trace" in record:
                raise CensusError(
                    f"ingest resource-limit unexpectedly has a route trace for {record['file']}"
                )
            trace = None
            decline = {
                "route": "smtlib-ingest",
                "reason": "resource-limit",
                "kind": "ResourceLimit",
                "detail": detail,
            }
        else:
            raise CensusError(f"trace capture is incomplete for {record.get('file')}")
        key = (decline["route"], decline["reason"], decline.get("kind", ""))
        buckets[key] += 1
        cases.append(
            {
                "file": record["file"],
                "verdict": record.get("verdict"),
                "first_causal_decline": decline,
                "trace": trace,
            }
        )

    return {
        "schema": "axeyum-qf-nia-a3-causal-census-v2",
        "trace_jsonl_path": str(trace_path),
        "trace_jsonl_sha256": sha256_file(trace_path),
        "rows": len(cases),
        "classification_rule": (
            "ingest-resource-limit maps to smtlib-ingest/resource-limit/ResourceLimit; "
            "otherwise first ordered declined attempt after probe whose reason is neither "
            "not-applicable nor unsupported"
        ),
        "buckets": [
            {"route": route, "reason": reason, "kind": kind or None, "count": count}
            for (route, reason, kind), count in sorted(buckets.items())
        ],
        "cases": cases,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--population", type=pathlib.Path, required=True)
    parser.add_argument("--sidecar", type=pathlib.Path, required=True)
    parser.add_argument("--population-sha256", required=True)
    parser.add_argument("--sidecar-sha256", required=True)
    parser.add_argument("--expected-rows", type=int, required=True)
    parser.add_argument("--expected-reference-only", type=int, required=True)
    parser.add_argument("--output-list", type=pathlib.Path, required=True)
    parser.add_argument("--output-sidecar-copy", type=pathlib.Path)
    parser.add_argument("--trace-jsonl", type=pathlib.Path)
    parser.add_argument("--output-census", type=pathlib.Path)
    args = parser.parse_args()
    try:
        if (args.trace_jsonl is None) != (args.output_census is None):
            raise CensusError("--trace-jsonl and --output-census must be supplied together")
        residual, summary = extract(
            args.population,
            args.sidecar,
            expected_population_sha256=args.population_sha256,
            expected_sidecar_sha256=args.sidecar_sha256,
            expected_rows=args.expected_rows,
            expected_reference_only=args.expected_reference_only,
        )
        args.output_list.parent.mkdir(parents=True, exist_ok=True)
        args.output_list.write_text("".join(f"{entry}\n" for entry in residual), encoding="utf-8")
        if args.output_sidecar_copy is not None:
            args.output_sidecar_copy.parent.mkdir(parents=True, exist_ok=True)
            args.output_sidecar_copy.write_bytes(args.sidecar.read_bytes())
        if args.trace_jsonl is not None:
            census = analyze_traces(residual, args.trace_jsonl)
            args.output_census.parent.mkdir(parents=True, exist_ok=True)
            args.output_census.write_text(
                json.dumps(census, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
            summary["census_path"] = str(args.output_census)
            summary["census_sha256"] = sha256_file(args.output_census)
        print(json.dumps(summary, sort_keys=True, separators=(",", ":")))
        return 0
    except (CensusError, OSError) as error:
        print(f"qf-nia-a3-census: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
