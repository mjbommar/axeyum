#!/usr/bin/env python3
"""Fail-closed analysis of a preregistered usbprint policy/resource frontier."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
from typing import Any


RUNNER_PATH = Path(__file__).with_name("run-glaurung-usbprint-frontier.py")
RUNNER_SPEC = importlib.util.spec_from_file_location("usbprint_frontier_runner", RUNNER_PATH)
assert RUNNER_SPEC and RUNNER_SPEC.loader
RUNNER = importlib.util.module_from_spec(RUNNER_SPEC)
RUNNER_SPEC.loader.exec_module(RUNNER)

OUTPUT_SCHEMA = "axeyum.glaurung-usbprint-frontier-analysis.v1"


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise RuntimeError(f"expected JSON object: {path}")
    return value


def _clean_identity(value: Any, revision: str | None = None) -> bool:
    return (
        isinstance(value, dict)
        and isinstance(value.get("revision"), str)
        and bool(value["revision"])
        and value.get("tracked_dirty") is False
        and (revision is None or value["revision"] == revision)
    )


def _expected_work(point: dict[str, Any]) -> dict[str, int]:
    return {
        "IOCTLANCE_DEADLINE_SECS": point["work"]["deadline_secs"],
        "IOCTLANCE_MAX_ANALYZED_FUNCTIONS": point["max_analyzed_functions"],
        "IOCTLANCE_SOLVE_BUDGET": point["work"]["solve_budget"],
        "IOCTLANCE_SOLVE_SECS": point["work"]["solve_secs"],
        "GLAURUNG_CHECK_TIMEOUT_MS": point["work"]["check_timeout_ms"],
    }


def _validate_complete_report(
    report: dict[str, Any],
    registration: dict[str, Any],
    point: dict[str, Any],
    policy: dict[str, Any],
    failures: list[str],
    label: str,
) -> dict[str, Any]:
    if report.get("schema") != "axeyum.glaurung-authoritative-finding-parity.v5":
        failures.append(f"{label}: unsupported authority report schema")
    if report.get("accepted") is not True or report.get("failures") != []:
        failures.append(f"{label}: authority report was not accepted")
    if report.get("acceptance_population") != "high-confidence":
        failures.append(f"{label}: wrong acceptance population")
    if report.get("all_drivers_exact_high_confidence_finding_parity") is not True:
        failures.append(f"{label}: lacks high-confidence authority parity")
    if report.get("concretization_policy_id") != policy["policy_id"]:
        failures.append(f"{label}: policy identity differs")
    if not _clean_identity(report.get("glaurung"), registration["glaurung_revision"]):
        failures.append(f"{label}: Glaurung source identity differs")
    if not _clean_identity(report.get("axeyum")):
        failures.append(f"{label}: Axeyum source identity is not clean")
    post = report.get("post_run_source_identity")
    if not isinstance(post, dict) or post.get("stable") is not True:
        failures.append(f"{label}: source identity changed during measurement")
    binaries = report.get("binaries")
    for backend in ("z3", "axeyum"):
        observed = binaries.get(backend) if isinstance(binaries, dict) else None
        if not isinstance(observed, dict) or observed.get("sha256") != registration[
            "authority_binary_sha256"
        ][backend]:
            failures.append(f"{label}: {backend} authority binary identity differs")
    environment = report.get("environment")
    for key, expected in _expected_work(point).items():
        if not isinstance(environment, dict) or environment.get(key) != str(expected):
            failures.append(f"{label}: work field {key} differs")
    if report.get("process_timeout_seconds") != point["work"]["process_timeout_secs"]:
        failures.append(f"{label}: process timeout differs")
    if report.get("repetitions") != point["work"]["repetitions"]:
        failures.append(f"{label}: repetition count differs")

    drivers = report.get("drivers")
    if not isinstance(drivers, list) or len(drivers) != 1:
        failures.append(f"{label}: driver population differs")
        return {"high": 0, "runs": []}
    driver = drivers[0]
    identity = driver.get("driver") if isinstance(driver, dict) else None
    if not isinstance(identity, dict) or identity.get("sha256") != registration["driver"][
        "sha256"
    ]:
        failures.append(f"{label}: usbprint identity differs")
    summary = driver.get("summary") if isinstance(driver, dict) else None
    if not isinstance(summary, dict) or driver.get("summary_error") is not None:
        failures.append(f"{label}: driver summary is missing")
        return {"high": 0, "runs": []}
    coverage = summary.get("coverage")
    limit = point["max_analyzed_functions"]
    if not isinstance(coverage, dict) or any(
        (
            coverage.get("analyzed") != limit,
            coverage.get("boundary") != "fixed-work-limit",
            not isinstance(coverage.get("reachable"), int)
            or coverage["reachable"] <= limit,
        )
    ):
        failures.append(f"{label}: fixed function-prefix coverage differs")
    if summary.get("confidence_partition_available") is not True:
        failures.append(f"{label}: confidence partition is unavailable")
    high = summary.get("high_confidence")
    if not isinstance(high, dict) or high.get("exact_finding_parity") is not True:
        failures.append(f"{label}: high-confidence summary differs")
    backend_summary = summary.get("backends")
    high_counts: list[int] = []
    for backend in ("z3", "axeyum"):
        row = backend_summary.get(backend) if isinstance(backend_summary, dict) else None
        count = row.get("high_confidence_finding_count") if isinstance(row, dict) else None
        if not isinstance(count, int):
            failures.append(f"{label}: {backend} high-confidence count is missing")
        else:
            high_counts.append(count)
    if high_counts and any(count != 0 for count in high_counts):
        failures.append(f"{label}: corrected usbprint produced a high-confidence row")

    runs = driver.get("runs")
    if not isinstance(runs, list) or len(runs) != 4:
        failures.append(f"{label}: run population differs")
        runs = []
    expected_order = [
        ("z3", 1, 1),
        ("axeyum", 1, 2),
        ("axeyum", 2, 1),
        ("z3", 2, 2),
    ]
    observed_order = [
        (run.get("backend"), run.get("repetition"), run.get("position"))
        for run in runs
        if isinstance(run, dict)
    ]
    if observed_order != expected_order:
        failures.append(f"{label}: order-balanced run population differs")
    run_rows: list[dict[str, Any]] = []
    for index, run in enumerate(runs):
        if not isinstance(run, dict):
            continue
        if (
            run.get("analyzed") != limit
            or run.get("coverage_boundary") != "fixed-work-limit"
            or run.get("check_timeout_ms") != point["work"]["check_timeout_ms"]
            or run.get("canonical_model_choice", {}).get("policy") != policy["policy_id"]
        ):
            failures.append(f"{label}: run {index} work or policy telemetry differs")
        for key in ("solves", "elapsed_seconds", "max_rss_kib", "finding_count"):
            if not isinstance(run.get(key), (int, float)):
                failures.append(f"{label}: run {index} lacks {key}")
        if run.get("high_confidence_finding_count") != 0:
            failures.append(f"{label}: run {index} has nonzero high-confidence output")
        run_rows.append(
            {
                key: run.get(key)
                for key in (
                    "backend",
                    "repetition",
                    "position",
                    "solves",
                    "elapsed_seconds",
                    "max_rss_kib",
                    "finding_count",
                    "diagnostic_finding_count",
                )
            }
        )
    return {"high": max(high_counts, default=0), "runs": run_rows, "coverage": coverage}


def analyze_frontier(
    registration: dict[str, Any],
    execution: dict[str, Any],
    reports: dict[tuple[str, str], dict[str, Any]],
    *,
    registration_sha256: str,
    report_hashes: dict[tuple[str, str], str],
) -> dict[str, Any]:
    failures: list[str] = []
    try:
        RUNNER.validate_registration(registration)
    except RuntimeError as error:
        failures.append(str(error))
    if execution.get("schema") != RUNNER.EXECUTION_SCHEMA:
        failures.append("unsupported frontier execution schema")
    if execution.get("registration_sha256") != registration_sha256:
        failures.append("execution registration SHA-256 differs")
    if execution.get("source_identity_stable") is not True:
        failures.append("execution source identity changed")
    if not _clean_identity(execution.get("glaurung"), registration.get("glaurung_revision")):
        failures.append("execution Glaurung identity differs")
    if not _clean_identity(execution.get("axeyum")):
        failures.append("execution Axeyum identity is not clean")

    expected_order = RUNNER.cell_order(registration)
    cells = execution.get("cells")
    if not isinstance(cells, list) or not cells:
        failures.append("execution has no cells")
        cells = []
    observed_order = [
        (cell.get("point"), cell.get("policy"))
        for cell in cells
        if isinstance(cell, dict)
    ]
    if observed_order != expected_order[: len(observed_order)]:
        failures.append("execution cell order is not the preregistered point-major prefix")

    point_by_label = {point["label"]: point for point in registration.get("points", [])}
    policy_by_label = {policy["label"]: policy for policy in registration.get("policies", [])}
    complete_by_point: dict[str, set[str]] = {
        point["label"]: set() for point in registration.get("points", [])
    }
    per_policy_max = {policy["label"]: 0 for policy in registration.get("policies", [])}
    cell_results: list[dict[str, Any]] = []
    high_count = 0
    first_resource: list[str] | None = None
    for index, cell in enumerate(cells):
        if not isinstance(cell, dict):
            failures.append(f"execution cell {index} is malformed")
            continue
        key = (cell.get("point"), cell.get("policy"))
        point = point_by_label.get(key[0])
        policy = policy_by_label.get(key[1])
        if point is None or policy is None:
            failures.append(f"execution cell {index} has unknown identity")
            continue
        report = reports.get(key)
        if report is None:
            failures.append(f"execution cell {index} report is missing")
            continue
        observed_hash = report_hashes.get(key)
        if cell.get("report_sha256") != observed_hash:
            failures.append(f"execution cell {index} report SHA-256 differs")
        classification = RUNNER.classify_report(report)
        if cell.get("classification") != classification:
            failures.append(f"execution cell {index} classification differs")
        if classification == "complete":
            details = _validate_complete_report(
                report, registration, point, policy, failures, f"{key[0]}/{key[1]}"
            )
            high_count += details["high"]
            complete_by_point[key[0]].add(key[1])
            per_policy_max[key[1]] = max(
                per_policy_max[key[1]], point["max_analyzed_functions"]
            )
            cell_results.append({"point": key[0], "policy": key[1], "classification": classification, **details})
        elif classification == "resource-bound":
            if index != len(cells) - 1:
                failures.append("resource-bound cell is not the final executed cell")
            first_resource = [key[0], key[1]]
            cell_results.append({"point": key[0], "policy": key[1], "classification": classification})
        else:
            failures.append(f"{key[0]}/{key[1]} is a protocol failure")

    if len(cells) < len(expected_order) and not first_resource:
        failures.append("partial execution lacks a pure resource-bound stop")
    matrix_complete = len(cells) == len(expected_order) and all(
        cell.get("classification") == "complete" for cell in cells if isinstance(cell, dict)
    )
    policy_labels = set(policy_by_label)
    complete_limits = [
        point["max_analyzed_functions"]
        for point in registration.get("points", [])
        if complete_by_point.get(point["label"]) == policy_labels
    ]
    common_completed_prefix = max(complete_limits, default=0)
    if common_completed_prefix == 0:
        failures.append("no complete common prefix exists across all five policies")
    return {
        "schema": OUTPUT_SCHEMA,
        "accepted": not failures,
        "registration_sha256": registration_sha256,
        "matrix_complete": matrix_complete,
        "executed_cell_count": len(cells),
        "expected_cell_count": len(expected_order),
        "common_completed_prefix": common_completed_prefix,
        "per_policy_completed_prefix": per_policy_max,
        "first_resource_bound": first_resource,
        "high_confidence_finding_count": high_count,
        "cells": cell_results,
        "failures": failures,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", type=Path, required=True)
    parser.add_argument("--execution", type=Path, required=True)
    parser.add_argument("--result-dir", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    registration = load_json(args.registration)
    execution = load_json(args.execution)
    reports: dict[tuple[str, str], dict[str, Any]] = {}
    report_hashes: dict[tuple[str, str], str] = {}
    for cell in execution.get("cells", []):
        if not isinstance(cell, dict):
            continue
        key = (cell.get("point"), cell.get("policy"))
        report_path = args.result_dir / cell.get("report", "")
        if report_path.is_file():
            reports[key] = load_json(report_path)
            report_hashes[key] = file_sha256(report_path)
    result = analyze_frontier(
        registration,
        execution,
        reports,
        registration_sha256=file_sha256(args.registration),
        report_hashes=report_hashes,
    )
    if args.out.exists():
        raise RuntimeError(f"refusing to overwrite {args.out}")
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
