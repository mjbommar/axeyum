#!/usr/bin/env python3
"""Fail-closed repeated gate for Glaurung native ordered replay reports."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import statistics
import sys
from pathlib import Path
from typing import Any, NoReturn, Sequence


REPORT_SCHEMA = "glaurung-native-ordered-replay-report-v1"
SUMMARY_SCHEMA = "axeyum-glaurung-native-replay-comparison-v1"
RSS_PATTERN = re.compile(r"Maximum resident set size \(kbytes\):\s*([0-9]+)")
ELAPSED_PATTERN = re.compile(
    r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*([^\s]+)"
)


class GateError(ValueError):
    """A report or comparison violates the native replay contract."""


def fail(message: str) -> NoReturn:
    raise GateError(message)


def mapping(value: Any, location: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{location} must be a JSON object")
    return value


def integer(value: Any, location: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        fail(f"{location} must be a non-negative integer")
    return value


def load_report(path: Path) -> tuple[dict[str, Any], str]:
    try:
        data = path.read_bytes()
        value = json.loads(data)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"read {path}: {error}")
    report = mapping(value, str(path))
    if report.get("schema") != REPORT_SCHEMA or report.get("gate") != "pass":
        fail(f"{path}: report schema/gate is not a passing native replay v1")
    return report, hashlib.sha256(data).hexdigest()


def parse_elapsed(value: str, path: Path) -> float:
    try:
        pieces = [float(piece) for piece in value.split(":")]
    except ValueError:
        fail(f"{path}: invalid GNU time elapsed value {value!r}")
    if len(pieces) == 2:
        return pieces[0] * 60.0 + pieces[1]
    if len(pieces) == 3:
        return pieces[0] * 3600.0 + pieces[1] * 60.0 + pieces[2]
    fail(f"{path}: invalid GNU time elapsed value {value!r}")


def load_time(path: Path) -> tuple[int, float]:
    try:
        text = path.read_text()
    except OSError as error:
        fail(f"read {path}: {error}")
    rss = RSS_PATTERN.search(text)
    elapsed = ELAPSED_PATTERN.search(text)
    if rss is None or elapsed is None or "Exit status: 0" not in text:
        fail(f"{path}: incomplete or unsuccessful GNU time -v artifact")
    return int(rss.group(1)), parse_elapsed(elapsed.group(1), path)


def distribution(values: Sequence[float]) -> dict[str, float]:
    if not values:
        fail("cannot summarize an empty distribution")
    ordered = sorted(values)
    mean = statistics.fmean(ordered)
    deviation = statistics.stdev(ordered) if len(ordered) > 1 else 0.0
    return {
        "min": ordered[0],
        "p50": statistics.median(ordered),
        "max": ordered[-1],
        "mean": mean,
        "sample_standard_deviation": deviation,
        "coefficient_of_variation_percent": deviation / mean * 100.0
        if mean
        else 0.0,
    }


def percent_change(control: float, candidate: float) -> float:
    if control <= 0.0:
        fail("control metric must be positive")
    return (candidate / control - 1.0) * 100.0


def identity(report: dict[str, Any]) -> dict[str, Any]:
    outcomes = mapping(report.get("outcomes"), "outcomes")
    return {
        "trace": mapping(report.get("trace"), "trace"),
        "bindings": mapping(report.get("bindings"), "bindings"),
        "implementation": mapping(report.get("implementation"), "implementation"),
        "recorded_outcomes": {
            key: integer(outcomes.get(key), f"outcomes.{key}")
            for key in (
                "recorded_sat",
                "recorded_unsat",
                "recorded_unknown",
                "recorded_error",
            )
        },
        "exact_work": mapping(report.get("exact_work"), "exact_work"),
        "ownership": mapping(report.get("ownership"), "ownership"),
    }


def validate_zeroes(report: dict[str, Any], path: Path) -> None:
    outcomes = mapping(report.get("outcomes"), f"{path}: outcomes")
    exact = mapping(report.get("exact_work"), f"{path}: exact_work")
    ownership = mapping(report.get("ownership"), f"{path}: ownership")
    cache = mapping(report.get("replay_sat_cache"), f"{path}: replay_sat_cache")
    required_zeroes = {
        "outcomes.opposite_decisions": outcomes.get("opposite_decisions"),
        "exact_work.synchronization_mismatches": exact.get(
            "synchronization_mismatches"
        ),
        "exact_work.resets_after_error": exact.get("resets_after_error"),
        "ownership.live_paths": ownership.get("live_paths"),
        "ownership.serial_tracked_owners": ownership.get("serial_tracked_owners"),
        "ownership.serial_references": ownership.get("serial_references"),
        "replay_sat_cache.replay_failures": cache.get("replay_failures"),
    }
    for name, value in required_zeroes.items():
        if integer(value, f"{path}: {name}") != 0:
            fail(f"{path}: {name} must be zero")


def validate_policy(report: dict[str, Any], path: Path, candidate: bool) -> None:
    validate_zeroes(report, path)
    config = mapping(report.get("configuration"), f"{path}: configuration")
    expected = "1" if candidate else "0"
    if config.get("GLAURUNG_AXEYUM_WARM_TIMEOUT_CONTINUE") != expected:
        fail(f"{path}: continuation configuration must be {expected}")
    continuation = mapping(
        report.get("timeout_continuation"), f"{path}: timeout_continuation"
    )
    attempts = integer(continuation.get("continuations"), f"{path}: continuations")
    partition = sum(
        integer(continuation.get(key), f"{path}: {key}")
        for key in ("recoveries", "unknowns", "errors")
    )
    if attempts != partition or integer(continuation.get("errors"), "errors") != 0:
        fail(f"{path}: continuation counters do not form an error-free partition")
    if not candidate and attempts != 0:
        fail(f"{path}: control unexpectedly continued an unknown")
    if integer(continuation.get("cold_retries"), f"{path}: cold_retries") != 0:
        fail(f"{path}: cold retry must remain disabled")


def summarize(
    reports: Sequence[Path],
    times: Sequence[Path],
    *,
    candidate: bool,
) -> tuple[dict[str, Any], dict[str, Any]]:
    if len(reports) != len(times):
        fail("each report requires one matching GNU time artifact")
    loaded: list[dict[str, Any]] = []
    hashes: list[str] = []
    rss: list[float] = []
    elapsed: list[float] = []
    native: list[float] = []
    expected_identity: dict[str, Any] | None = None
    recoveries = 0
    continuations = 0
    for report_path, time_path in zip(reports, times, strict=True):
        report, digest = load_report(report_path)
        validate_policy(report, report_path, candidate)
        current_identity = identity(report)
        if expected_identity is None:
            expected_identity = current_identity
        elif current_identity != expected_identity:
            fail(f"{report_path}: exact trace/work identity drift within policy")
        timing = mapping(report.get("timing"), f"{report_path}: timing")
        native.append(
            integer(timing.get("actual_axeyum_nanos"), "actual_axeyum_nanos")
            / 1_000_000_000.0
        )
        run_rss, run_elapsed = load_time(time_path)
        rss.append(float(run_rss))
        elapsed.append(run_elapsed)
        continuation = mapping(report["timeout_continuation"], "continuation")
        recoveries += integer(continuation.get("recoveries"), "recoveries")
        continuations += integer(continuation.get("continuations"), "continuations")
        hashes.append(digest)
        loaded.append(report)
    assert expected_identity is not None
    return (
        {
            "runs": len(loaded),
            "report_sha256": hashes,
            "axeyum_seconds": distribution(native),
            "process_elapsed_seconds": distribution(elapsed),
            "maximum_rss_kib": distribution(rss),
            "continuations": continuations,
            "recoveries": recoveries,
        },
        expected_identity,
    )


def compare(args: argparse.Namespace) -> dict[str, Any]:
    if len(args.control_report) < args.min_repetitions or len(
        args.candidate_report
    ) < args.min_repetitions:
        fail(f"each policy requires at least {args.min_repetitions} repetitions")
    control, control_identity = summarize(
        args.control_report, args.control_time, candidate=False
    )
    candidate, candidate_identity = summarize(
        args.candidate_report, args.candidate_time, candidate=True
    )
    if control_identity != candidate_identity:
        fail("control/candidate trace, finding, or exact-work identity differs")
    if candidate["continuations"] == 0 or candidate["recoveries"] == 0:
        fail("candidate must exercise continuation and recover a decision")

    control_time = control["axeyum_seconds"]["p50"]
    candidate_time = candidate["axeyum_seconds"]["p50"]
    control_rss = control["maximum_rss_kib"]["p50"]
    candidate_rss = candidate["maximum_rss_kib"]["p50"]
    time_change = percent_change(control_time, candidate_time)
    rss_change = percent_change(control_rss, candidate_rss)
    for policy, summary in (("control", control), ("candidate", candidate)):
        cv = summary["axeyum_seconds"]["coefficient_of_variation_percent"]
        if cv > args.max_cv_percent:
            fail(f"{policy} Axeyum time CV {cv:.3f}% exceeds {args.max_cv_percent:.3f}%")
    if time_change > args.max_time_regression_percent:
        fail(
            f"candidate Axeyum p50 regression {time_change:.3f}% exceeds "
            f"{args.max_time_regression_percent:.3f}%"
        )
    if rss_change > args.max_rss_regression_percent:
        fail(
            f"candidate RSS p50 regression {rss_change:.3f}% exceeds "
            f"{args.max_rss_regression_percent:.3f}%"
        )
    return {
        "schema": SUMMARY_SCHEMA,
        "identity": control_identity,
        "alarms": {
            "max_time_regression_percent": args.max_time_regression_percent,
            "max_rss_regression_percent": args.max_rss_regression_percent,
            "max_cv_percent": args.max_cv_percent,
        },
        "control": control,
        "candidate": candidate,
        "changes_percent": {
            "axeyum_p50": time_change,
            "maximum_rss_p50": rss_change,
        },
        "gate": "pass",
    }


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--control-report", type=Path, action="append", required=True)
    result.add_argument("--control-time", type=Path, action="append", required=True)
    result.add_argument("--candidate-report", type=Path, action="append", required=True)
    result.add_argument("--candidate-time", type=Path, action="append", required=True)
    result.add_argument("--min-repetitions", type=int, default=3)
    result.add_argument("--max-time-regression-percent", type=float, default=3.0)
    result.add_argument("--max-rss-regression-percent", type=float, default=5.0)
    result.add_argument("--max-cv-percent", type=float, default=3.0)
    result.add_argument("--out", type=Path, required=True)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        summary = compare(args)
        data = json.dumps(summary, indent=2, sort_keys=True) + "\n"
        temporary = args.out.with_name(f".{args.out.name}.tmp.{os.getpid()}")
        temporary.write_text(data)
        temporary.replace(args.out)
    except (GateError, OSError) as error:
        print(f"native replay comparison failed: {error}", file=sys.stderr)
        return 1
    print(
        "native replay comparison passed: "
        f"time={summary['changes_percent']['axeyum_p50']:+.3f}% "
        f"rss={summary['changes_percent']['maximum_rss_p50']:+.3f}%"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
