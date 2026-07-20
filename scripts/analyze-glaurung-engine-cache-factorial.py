#!/usr/bin/env python3
"""Fail-closed analysis for ADR-0303's engine-cache/warm-state factorial."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import pathlib
import random
import re
import statistics
import sys
from typing import Any, NoReturn, Sequence


REGISTRATION_SCHEMA = "axeyum-glaurung-engine-cache-factorial-registration-v1"
CAMPAIGN_SCHEMA = "axeyum-glaurung-engine-cache-factorial-campaign-v1"
REPORT_SCHEMA = "glaurung-native-ordered-replay-report-v2"
RESULT_SCHEMA = "axeyum-glaurung-engine-cache-factorial-analysis-v1"
MODES = (
    "cold-off",
    "warm-off",
    "cold-exact",
    "warm-exact",
    "cold-structural",
    "warm-structural",
)
CONTRASTS = (
    ("cold-off_over_warm-off", "cold-off", "warm-off"),
    ("cold-off_over_cold-exact", "cold-off", "cold-exact"),
    ("warm-off_over_warm-exact", "warm-off", "warm-exact"),
    ("cold-exact_over_warm-exact", "cold-exact", "warm-exact"),
    ("cold-off_over_cold-structural", "cold-off", "cold-structural"),
    ("warm-off_over_warm-structural", "warm-off", "warm-structural"),
    ("cold-structural_over_warm-structural", "cold-structural", "warm-structural"),
    ("cold-exact_over_cold-structural", "cold-exact", "cold-structural"),
    ("warm-exact_over_warm-structural", "warm-exact", "warm-structural"),
)
CACHE_CLASSES = ("exact-sat", "exact-unsat", "sat-superset", "unsat-subset", "miss")
RSS_PATTERN = re.compile(r"Maximum resident set size \(kbytes\):\s*([0-9]+)")
ELAPSED_PATTERN = re.compile(
    r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*([^\s]+)"
)


class AnalysisError(ValueError):
    """A campaign artifact violates the preregistered contract."""


def fail(message: str) -> NoReturn:
    raise AnalysisError(message)


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def mapping(value: Any, location: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{location} must be a JSON object")
    return value


def sequence(value: Any, location: str) -> list[Any]:
    if not isinstance(value, list):
        fail(f"{location} must be a JSON array")
    return value


def integer(value: Any, location: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        fail(f"{location} must be a non-negative integer")
    return value


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_object(path: pathlib.Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_bytes())
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"cannot read {label} {path}: {error}")
    return mapping(value, label)


def resolve(root: pathlib.Path, raw: Any, location: str) -> pathlib.Path:
    require(isinstance(raw, str) and raw, f"{location} path is invalid")
    path = pathlib.Path(raw)
    return path if path.is_absolute() else root / path


def parse_elapsed(value: str, path: pathlib.Path) -> float:
    try:
        pieces = [float(piece) for piece in value.split(":")]
    except ValueError:
        fail(f"{path}: invalid elapsed time {value!r}")
    if len(pieces) == 2:
        return pieces[0] * 60.0 + pieces[1]
    if len(pieces) == 3:
        return pieces[0] * 3600.0 + pieces[1] * 60.0 + pieces[2]
    fail(f"{path}: invalid elapsed time {value!r}")


def load_external_time(path: pathlib.Path) -> dict[str, float]:
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as error:
        fail(f"cannot read external time {path}: {error}")
    rss = RSS_PATTERN.search(text)
    elapsed = ELAPSED_PATTERN.search(text)
    require(rss is not None and elapsed is not None, f"{path}: incomplete GNU time artifact")
    require("Exit status: 0" in text, f"{path}: unsuccessful GNU time artifact")
    return {
        "maximum_rss_kib": float(rss.group(1)),
        "elapsed_seconds": parse_elapsed(elapsed.group(1), path),
    }


def geometric_mean(values: Sequence[float]) -> float:
    require(bool(values), "geometric mean requires values")
    require(all(math.isfinite(value) and value > 0.0 for value in values), "geometric mean requires finite positive values")
    return math.exp(statistics.fmean(math.log(value) for value in values))


def nearest_rank(values: Sequence[float], quantile: float) -> float:
    require(bool(values) and 0.0 < quantile <= 1.0, "invalid nearest-rank input")
    ordered = sorted(values)
    return ordered[max(0, math.ceil(quantile * len(ordered)) - 1)]


def distribution(values: Sequence[float]) -> dict[str, float]:
    require(bool(values), "cannot summarize an empty distribution")
    mean = statistics.fmean(values)
    deviation = statistics.stdev(values) if len(values) > 1 else 0.0
    return {
        "min": min(values),
        "p50": nearest_rank(values, 0.50),
        "p90": nearest_rank(values, 0.90),
        "p95": nearest_rank(values, 0.95),
        "p99": nearest_rank(values, 0.99),
        "max": max(values),
        "mean": mean,
        "sample_standard_deviation": deviation,
        "coefficient_of_variation": deviation / mean if mean else 0.0,
    }


def bootstrap_geomean_ci(values: Sequence[float], samples: int, seed: int) -> list[float]:
    require(samples == 10_000, "bootstrap sample count must remain 10,000")
    rng = random.Random(seed)
    estimates = [
        geometric_mean([values[rng.randrange(len(values))] for _ in values])
        for _ in range(samples)
    ]
    return [nearest_rank(estimates, 0.025), nearest_rank(estimates, 0.975)]


def check_identity(report: dict[str, Any]) -> tuple[tuple[Any, ...], ...]:
    rows = sequence(report.get("checks"), "checks")
    return tuple(
        (
            integer(row.get("index"), "check.index"),
            row.get("query_sha256"),
            row.get("recorded_outcome"),
            integer(row.get("assertion_count"), "check.assertion_count"),
            integer(row.get("owner_id"), "check.owner_id"),
        )
        for row in (mapping(item, "check") for item in rows)
    )


def validate_report(
    report: dict[str, Any],
    path: pathlib.Path,
    mode: str,
    input_row: dict[str, Any],
    registration: dict[str, Any],
) -> dict[str, Any]:
    require(report.get("schema") == REPORT_SCHEMA and report.get("gate") == "pass", f"{path}: report is not passing v2")
    config = mapping(report.get("configuration"), f"{path}: configuration")
    require(config.get("factorial_mode") == mode, f"{path}: factorial mode differs")
    expected_policy = "off" if mode.endswith("off") else ("exact" if mode.endswith("exact") else "structural")
    require(config.get("GLAURUNG_ENGINE_CONSTRAINT_CACHE") == expected_policy, f"{path}: cache policy differs")
    expected_warm = "adaptive" if mode.startswith("warm") else "off"
    require(config.get("GLAURUNG_AXEYUM_WARM_REUSE") == expected_warm, f"{path}: warm policy differs")
    require(config.get("engine_cache_limits") == registration["protocol"]["cache_limits"], f"{path}: cache limits differ")

    trace = mapping(report.get("trace"), f"{path}: trace")
    require(trace.get("manifest_sha256") == input_row["manifest_sha256"], f"{path}: manifest binding differs")
    bindings = mapping(report.get("bindings"), f"{path}: bindings")
    require(bindings.get("finding_sha256") == input_row["finding_sha256"], f"{path}: finding binding differs")
    require(bindings.get("offline_replay_sha256") == input_row["offline_replay_sha256"], f"{path}: offline replay binding differs")
    implementation = mapping(report.get("implementation"), f"{path}: implementation")
    require(implementation.get("replay_executable_sha256") == registration["executable"]["sha256"], f"{path}: executable binding differs")
    require(implementation.get("glaurung_replay_revision") == registration["sources"]["glaurung"]["revision"], f"{path}: Glaurung revision differs")
    axeyum_source = mapping(implementation.get("axeyum_source"), f"{path}: Axeyum source")
    require(axeyum_source.get("revision") == registration["sources"]["axeyum"]["revision"], f"{path}: Axeyum revision differs")
    require(axeyum_source.get("tracked_dirty") is False, f"{path}: Axeyum source is dirty")

    outcomes = mapping(report.get("outcomes"), f"{path}: outcomes")
    required_zeroes = (
        "recorded_unknown",
        "recorded_error",
        "actual_unknown",
        "recovered_decisions",
        "lost_decisions",
        "opposite_decisions",
    )
    for key in required_zeroes:
        require(integer(outcomes.get(key), f"{path}: outcomes.{key}") == 0, f"{path}: outcomes.{key} must be zero")
    require(outcomes.get("recorded_sat") == outcomes.get("actual_sat"), f"{path}: SAT population differs")
    require(outcomes.get("recorded_unsat") == outcomes.get("actual_unsat"), f"{path}: UNSAT population differs")

    exact = mapping(report.get("exact_work"), f"{path}: exact_work")
    ownership = mapping(report.get("ownership"), f"{path}: ownership")
    replay_cache = mapping(report.get("replay_sat_cache"), f"{path}: replay_sat_cache")
    for location, value in {
        "synchronization_mismatches": exact.get("synchronization_mismatches"),
        "resets_after_error": exact.get("resets_after_error"),
        "live_paths": ownership.get("live_paths"),
        "serial_tracked_owners": ownership.get("serial_tracked_owners"),
        "serial_references": ownership.get("serial_references"),
        "replay_sat_cache.replay_failures": replay_cache.get("replay_failures"),
    }.items():
        require(integer(value, f"{path}: {location}") == 0, f"{path}: {location} must be zero")

    cache = mapping(report.get("engine_constraint_cache"), f"{path}: engine cache")
    rows = [mapping(row, f"{path}: check") for row in sequence(report.get("checks"), f"{path}: checks")]
    require(len(rows) == integer(trace.get("check_count"), f"{path}: trace.check_count"), f"{path}: check rows differ")
    class_counts = {name: 0 for name in CACHE_CLASSES}
    wrapper_total = 0
    for expected_index, row in enumerate(rows):
        require(integer(row.get("index"), f"{path}: check.index") == expected_index, f"{path}: check indices differ")
        cache_class = row.get("cache_class")
        require(cache_class in class_counts, f"{path}: unsupported cache class {cache_class!r}")
        class_counts[cache_class] += 1
        stages = sum(
            integer(row.get(key), f"{path}: check.{key}")
            for key in (
                "lookup_nanos",
                "model_replay_nanos",
                "index_update_nanos",
                "eviction_nanos",
                "backend_miss_nanos",
            )
        )
        wrapper = integer(row.get("wrapper_nanos"), f"{path}: check.wrapper_nanos")
        require(wrapper > 0 and stages <= wrapper, f"{path}: invalid non-overlapping stage timing")
        require(row.get("stage_slack_nanos") == wrapper - stages, f"{path}: stage slack differs")
        if cache_class == "miss":
            require(row.get("backend_called") is True, f"{path}: miss skipped backend")
        else:
            require(row.get("backend_called") is False, f"{path}: hit called backend")
            require(row.get("backend_miss_nanos") == 0, f"{path}: hit has backend time")
            require(row.get("warm_synchronized") is False, f"{path}: hit advanced warm synchronization")
        wrapper_total += wrapper
    check_count = len(rows)
    hits = sum(class_counts[name] for name in CACHE_CLASSES[:-1])
    require(integer(cache.get("lookups"), f"{path}: cache.lookups") == (0 if expected_policy == "off" else check_count), f"{path}: lookup count differs")
    if expected_policy == "off":
        require(hits == 0 and class_counts["miss"] == check_count, f"{path}: cache-off row classification differs")
        for key, value in cache.items():
            if key != "policy" and isinstance(value, int):
                require(value == 0, f"{path}: cache-off {key} must be zero")
    else:
        require(cache.get("exact_sat_hits") == class_counts["exact-sat"], f"{path}: exact SAT count differs")
        require(cache.get("exact_unsat_hits") == class_counts["exact-unsat"], f"{path}: exact UNSAT count differs")
        require(cache.get("sat_superset_hits") == class_counts["sat-superset"], f"{path}: SAT-superset count differs")
        require(cache.get("unsat_subset_hits") == class_counts["unsat-subset"], f"{path}: UNSAT-subset count differs")
        require(cache.get("misses") == class_counts["miss"], f"{path}: miss count differs")
        require(hits + class_counts["miss"] == check_count, f"{path}: cache partition differs")
        for key in ("sat_replay_failures", "sat_replay_missing_symbols", "conflicts"):
            require(integer(cache.get(key), f"{path}: cache.{key}") == 0, f"{path}: cache.{key} must be zero")
        if expected_policy == "exact":
            require(class_counts["sat-superset"] == 0 and class_counts["unsat-subset"] == 0, f"{path}: exact cache used implication")
    timing = mapping(report.get("timing"), f"{path}: timing")
    require(integer(timing.get("actual_axeyum_nanos"), f"{path}: actual Axeyum time") == wrapper_total, f"{path}: wrapper timing total differs")
    require(integer(timing.get("peak_rss_kib"), f"{path}: peak RSS") > 0, f"{path}: peak RSS is zero")
    return {
        "report": report,
        "identity": check_identity(report),
        "class_counts": class_counts,
        "wrapper_nanos": [float(row["wrapper_nanos"]) for row in rows],
        "process_geomean_nanos": geometric_mean([float(row["wrapper_nanos"]) for row in rows]),
        "cache": cache,
        "timing": timing,
    }


def expected_classification(
    loaded: dict[str, Any], expected: dict[str, Any], mode: str
) -> dict[str, Any]:
    cache = loaded["cache"]
    counts = loaded["class_counts"]
    bounded = integer(cache.get("evictions"), "cache.evictions") > 0 or integer(cache.get("oversize_bypasses"), "cache.oversize_bypasses") > 0
    if mode.endswith("off"):
        return {"bounded_delta": False, "matches_opportunity": True, "delta": {}}
    if mode.endswith("exact"):
        target = {
            "exact-sat": expected["exact_sat_hits"],
            "exact-unsat": expected["exact_unsat_hits"],
            "sat-superset": 0,
            "unsat-subset": 0,
            "miss": expected["checks"] - expected["exact_hits"],
        }
    else:
        target = {
            "exact-sat": expected["exact_sat_hits"],
            "exact-unsat": expected["exact_unsat_hits"],
            "sat-superset": expected["sat_superset_hits"],
            "unsat-subset": expected["unsat_subset_hits"],
            "miss": expected["misses"],
        }
    delta = {key: counts[key] - target[key] for key in CACHE_CLASSES}
    matches = all(value == 0 for value in delta.values())
    require(bounded or matches, f"{mode}: cache classification differs without eviction/bypass")
    return {"bounded_delta": bounded, "matches_opportunity": matches, "delta": delta}


def ratio_summary(
    numerator: list[dict[str, Any]],
    denominator: list[dict[str, Any]],
    samples: int,
    seed: int,
) -> dict[str, Any]:
    require(len(numerator) == len(denominator) == 5, "contrast requires five paired repetitions")
    count = len(numerator[0]["wrapper_nanos"])
    require(all(len(run["wrapper_nanos"]) == count for run in numerator + denominator), "check count differs across contrast")
    ratios = []
    for index in range(count):
        left = geometric_mean([run["wrapper_nanos"][index] for run in numerator])
        right = geometric_mean([run["wrapper_nanos"][index] for run in denominator])
        ratios.append(left / right)
    ci = bootstrap_geomean_ci(ratios, samples, seed)
    numerator_cv = distribution([run["process_geomean_nanos"] for run in numerator])["coefficient_of_variation"]
    denominator_cv = distribution([run["process_geomean_nanos"] for run in denominator])["coefficient_of_variation"]
    stable = numerator_cv <= 0.03 and denominator_cv <= 0.03
    if not stable:
        conclusion = "inconclusive-variance"
    elif ci[0] > 1.0:
        conclusion = "denominator-faster"
    elif ci[1] < 1.0:
        conclusion = "denominator-slower"
    else:
        conclusion = "not-distinguished"
    return {
        "ratio_direction": "numerator/denominator; greater than one favors denominator",
        "checks": count,
        "geometric_mean": geometric_mean(ratios),
        "bootstrap_95_percent_ci": ci,
        "bootstrap_samples": samples,
        "latency_ratio_nearest_rank": {
            "p50": nearest_rank(ratios, 0.50),
            "p90": nearest_rank(ratios, 0.90),
            "p95": nearest_rank(ratios, 0.95),
            "p99": nearest_rank(ratios, 0.99),
        },
        "per_process_geomean_cv": {
            "numerator": numerator_cv,
            "denominator": denominator_cv,
            "limit": 0.03,
        },
        "conclusive": stable,
        "conclusion": conclusion,
    }


def analyze(
    registration_path: pathlib.Path,
    campaign_path: pathlib.Path,
    axeyum_root: pathlib.Path,
) -> dict[str, Any]:
    registration = load_object(registration_path, "registration")
    require(registration.get("schema") == REGISTRATION_SCHEMA, "registration schema differs")
    campaign = load_object(campaign_path, "campaign")
    require(campaign.get("schema") == CAMPAIGN_SCHEMA, "campaign schema differs")
    require(campaign.get("terminal_status") == "complete", "campaign is incomplete")
    require(campaign.get("registration_sha256") == sha256_file(registration_path), "campaign registration hash differs")
    protocol = mapping(registration.get("protocol"), "protocol")
    require(tuple(protocol.get("modes", ())) == MODES, "mode order differs")
    inputs = [mapping(row, "input") for row in sequence(campaign.get("inputs"), "campaign.inputs")]
    runs = [mapping(row, "run") for row in sequence(campaign.get("runs"), "campaign.runs")]
    require(len(inputs) == 20 and len(runs) == 120, "campaign cardinality differs")
    expected_run_keys = [
        (mode, row["driver"], row["repetition"])
        for mode in MODES
        for row in inputs
    ]
    require([(row.get("mode"), row.get("driver"), row.get("repetition")) for row in runs] == expected_run_keys, "campaign run order differs")

    opportunity_row = mapping(registration["sources"]["opportunity"], "opportunity source")
    opportunity_path = resolve(axeyum_root, opportunity_row.get("path"), "opportunity")
    require(sha256_file(opportunity_path) == opportunity_row.get("sha256"), "opportunity SHA-256 differs")
    opportunity = load_object(opportunity_path, "opportunity")
    expected_by_driver = {
        row["label"]: mapping(row.get("per_process"), f"opportunity {row['label']}")
        for row in sequence(opportunity.get("drivers"), "opportunity.drivers")
    }

    loaded: dict[str, dict[str, list[dict[str, Any]]]] = {
        driver: {mode: [] for mode in MODES} for driver in protocol["driver_order"]
    }
    for run, input_row in zip(runs, inputs * len(MODES), strict=True):
        require(run.get("validation") == "accepted" and run.get("return_code") == 0, f"run is not accepted: {run.get('run')}")
        report_path = pathlib.Path(str(run.get("report_path", "")))
        time_path = pathlib.Path(str(run.get("time_path", "")))
        require(report_path.is_file() and time_path.is_file(), f"run artifacts are absent: {run.get('run')}")
        require(sha256_file(report_path) == run.get("report_sha256"), f"report hash differs: {run.get('run')}")
        report = load_object(report_path, "report")
        validated = validate_report(report, report_path, run["mode"], input_row, registration)
        validated["external_time"] = load_external_time(time_path)
        validated["classification"] = expected_classification(
            validated, expected_by_driver[run["driver"]], run["mode"]
        )
        loaded[run["driver"]][run["mode"]].append(validated)

    driver_results = []
    samples = integer(protocol.get("bootstrap_samples"), "bootstrap_samples")
    seed = integer(protocol.get("bootstrap_seed"), "bootstrap_seed")
    for driver_index, driver in enumerate(protocol["driver_order"]):
        cells = loaded[driver]
        baseline_identity = cells[MODES[0]][0]["identity"]
        for mode in MODES:
            require(len(cells[mode]) == 5, f"{driver}/{mode}: repetition count differs")
            for repetition in cells[mode]:
                require(repetition["identity"] == baseline_identity, f"{driver}/{mode}: exact check identity differs")
        modes = {}
        for mode in MODES:
            modes[mode] = {
                "repetitions": 5,
                "checks_per_repetition": len(baseline_identity),
                "process_geomean_nanos": distribution(
                    [run["process_geomean_nanos"] for run in cells[mode]]
                ),
                "process_elapsed_seconds": distribution(
                    [run["external_time"]["elapsed_seconds"] for run in cells[mode]]
                ),
                "maximum_rss_kib": distribution(
                    [run["external_time"]["maximum_rss_kib"] for run in cells[mode]]
                ),
                "classification": [run["classification"] for run in cells[mode]],
                "cache": [run["cache"] for run in cells[mode]],
            }
        contrasts = {
            name: ratio_summary(
                cells[numerator],
                cells[denominator],
                samples,
                seed + driver_index * 100 + contrast_index,
            )
            for contrast_index, (name, numerator, denominator) in enumerate(CONTRASTS)
        }
        driver_results.append(
            {
                "driver": driver,
                "correctness_work_gate": "pass",
                "modes": modes,
                "contrasts": contrasts,
                "warm_additivity": {
                    "exact": contrasts["cold-exact_over_warm-exact"]["conclusion"],
                    "structural": contrasts["cold-structural_over_warm-structural"]["conclusion"],
                },
            }
        )
    return {
        "schema": RESULT_SCHEMA,
        "registration_sha256": sha256_file(registration_path),
        "campaign_sha256": sha256_file(campaign_path),
        "methodology": {
            "per_check_repetition_collapse": "geometric mean",
            "comparison": "paired per-check ratio, never ratio of sums",
            "quantiles": "nearest-rank",
            "bootstrap_samples": samples,
            "bootstrap_seed": seed,
            "cv_limit": 0.03,
            "headline_pooling": "forbidden; drivers reported separately",
        },
        "drivers": driver_results,
        "correctness_work_gate": "pass",
        "gate": "pass",
    }


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", required=True, type=pathlib.Path)
    parser.add_argument("--campaign", required=True, type=pathlib.Path)
    parser.add_argument("--axeyum-root", required=True, type=pathlib.Path)
    parser.add_argument("--out", required=True, type=pathlib.Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        result = analyze(
            args.registration.resolve(),
            args.campaign.resolve(),
            args.axeyum_root.resolve(),
        )
        temporary = args.out.with_name(f".{args.out.name}.tmp.{os.getpid()}")
        temporary.write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        temporary.replace(args.out)
    except (AnalysisError, OSError) as error:
        print(f"factorial analysis failed: {error}", file=sys.stderr)
        return 2
    print("factorial analysis passed; inspect each driver separately")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
