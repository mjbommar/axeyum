#!/usr/bin/env python3
"""Fail-closed analysis for repeated Axeyum/Z3/cvc5 QF_BV timeout sweeps."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import statistics
import tempfile
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, NoReturn, Sequence


SUPPORTED_SOURCE_ARTIFACT_VERSIONS = (32, 33)
ANALYSIS_SCHEMA = "axeyum-qfbv-timeout-sweep-analysis-v1"
CVC5_SCHEMA = "axeyum-qfbv-cvc5-timeout-sweep-v1"
DEFAULT_TIMEOUTS = (50, 100, 250, 1_000)
MIN_REPETITIONS = 5
POPULATIONS = (
    "both-decided",
    "axeyum-only-decided",
    "z3-only-decided",
    "neither-decided",
)


class AnalysisError(ValueError):
    """An input violates the timeout-sweep evidence contract."""


def fail(message: str) -> NoReturn:
    raise AnalysisError(message)


def mapping(value: Any, location: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{location} must be an object")
    return value


def sequence(value: Any, location: str) -> list[Any]:
    if not isinstance(value, list):
        fail(f"{location} must be an array")
    return value


def string(value: Any, location: str) -> str:
    if not isinstance(value, str) or not value:
        fail(f"{location} must be a non-empty string")
    return value


def integer(value: Any, location: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        fail(f"{location} must be an integer")
    return value


def number(value: Any, location: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        fail(f"{location} must be a number")
    result = float(value)
    if not math.isfinite(result):
        fail(f"{location} must be finite")
    return result


def boolean(value: Any, location: str) -> bool:
    if not isinstance(value, bool):
        fail(f"{location} must be a boolean")
    return value


def load_json(path: Path) -> tuple[dict[str, Any], str]:
    try:
        data = path.read_bytes()
        value = json.loads(
            data,
            parse_constant=lambda token: fail(f"{path}: non-finite number {token}"),
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"read {path}: {error}")
    return mapping(value, str(path)), "sha256:" + hashlib.sha256(data).hexdigest()


def percentile(values: Sequence[float], quantile: float) -> float:
    ordered = sorted(values)
    if not ordered:
        fail("cannot compute a percentile of an empty sample")
    position = (len(ordered) - 1) * quantile
    lower = math.floor(position)
    upper = math.ceil(position)
    if lower == upper:
        return ordered[lower]
    return ordered[lower] + (ordered[upper] - ordered[lower]) * (position - lower)


def distribution(values: Sequence[float]) -> dict[str, float | int]:
    if not values:
        fail("cannot summarize an empty sample")
    mean = statistics.fmean(values)
    deviation = statistics.stdev(values) if len(values) > 1 else 0.0
    return {
        "n": len(values),
        "min": min(values),
        "mean": mean,
        "sample_standard_deviation": deviation,
        "coefficient_of_variation_percent": 0.0
        if mean == 0.0
        else deviation / mean * 100.0,
        "p50": percentile(values, 0.50),
        "p90": percentile(values, 0.90),
        "p95": percentile(values, 0.95),
        "p99": percentile(values, 0.99),
        "max": max(values),
    }


def normalized_config(config: dict[str, Any]) -> dict[str, Any]:
    result = json.loads(json.dumps(config))
    result.pop("config_hash", None)
    result.pop("timeout_ms", None)
    resources = mapping(result.get("resources"), "config.resources")
    resources.pop("wall_clock_safety_timeout_ms", None)
    return result


def validate_config(config: dict[str, Any], path: Path) -> int:
    prefix = f"{path}: config"
    if config.get("backend_kind") != "sat-bv":
        fail(f"{prefix}.backend_kind must be sat-bv")
    if config.get("logic") != "QF_BV":
        fail(f"{prefix}.logic must be QF_BV")
    if config.get("jobs") != 1 or config.get("manifest_validation_jobs") != 1:
        fail(f"{prefix} must use one benchmark and manifest worker")
    if config.get("compare_z3") is not True:
        fail(f"{prefix}.compare_z3 must be true")
    if config.get("require_in_process_z3") is not True:
        fail(f"{prefix}.require_in_process_z3 must be true")
    if config.get("require_reproducible_run") is not True:
        fail(f"{prefix}.require_reproducible_run must be true")
    if mapping(config.get("rewrite"), f"{prefix}.rewrite").get("mode") != "off":
        fail(f"{prefix}.rewrite.mode must be off")
    source = mapping(
        mapping(config.get("experiment"), f"{prefix}.experiment").get("source"),
        f"{prefix}.experiment.source",
    )
    if boolean(source.get("dirty"), f"{prefix}.experiment.source.dirty"):
        fail(f"{prefix}.experiment.source.dirty must be false")
    timeout = integer(config.get("timeout_ms"), f"{prefix}.timeout_ms")
    if timeout <= 0:
        fail(f"{prefix}.timeout_ms must be positive")
    resource_timeout = integer(
        mapping(config.get("resources"), f"{prefix}.resources").get(
            "wall_clock_safety_timeout_ms"
        ),
        f"{prefix}.resources.wall_clock_safety_timeout_ms",
    )
    if resource_timeout != timeout:
        fail(f"{prefix} timeout fields disagree")
    return timeout


def population(primary: str, oracle: str) -> str:
    primary_decided = primary in ("sat", "unsat")
    oracle_decided = oracle in ("sat", "unsat")
    if primary_decided and oracle_decided:
        return "both-decided"
    if primary_decided:
        return "axeyum-only-decided"
    if oracle_decided:
        return "z3-only-decided"
    return "neither-decided"


def validate_axeyum_artifact(
    artifact: dict[str, Any], path: Path
) -> tuple[int, dict[str, dict[str, Any]], dict[str, Any]]:
    version = integer(artifact.get("version"), f"{path}: version")
    if version not in SUPPORTED_SOURCE_ARTIFACT_VERSIONS:
        fail(
            f"{path}: expected artifact version in "
            f"{SUPPORTED_SOURCE_ARTIFACT_VERSIONS}"
        )
    config = mapping(artifact.get("config"), f"{path}: config")
    timeout = validate_config(config, path)
    summary = mapping(artifact.get("summary"), f"{path}: summary")
    files = integer(summary.get("files"), f"{path}: summary.files")
    if files <= 0:
        fail(f"{path}: summary.files must be positive")
    for key in ("errors", "disagree", "model_replay_failures"):
        if integer(summary.get(key), f"{path}: summary.{key}") != 0:
            fail(f"{path}: summary.{key} must be zero")
    manifest_summary = mapping(summary.get("manifest"), f"{path}: summary.manifest")
    oracle_summary = mapping(summary.get("oracle"), f"{path}: summary.oracle")
    if integer(manifest_summary.get("disagree"), f"{path}: manifest.disagree") != 0:
        fail(f"{path}: manifest disagreement")
    if integer(oracle_summary.get("disagree"), f"{path}: oracle.disagree") != 0:
        fail(f"{path}: oracle disagreement")

    instances = sequence(artifact.get("instances"), f"{path}: instances")
    if len(instances) != files:
        fail(f"{path}: instances/files mismatch")
    by_file: dict[str, dict[str, Any]] = {}
    counts: Counter[str] = Counter()
    for index, raw in enumerate(instances):
        instance = mapping(raw, f"{path}: instances[{index}]")
        corpus = mapping(
            instance.get("corpus_manifest"),
            f"{path}: instances[{index}].corpus_manifest",
        )
        relative = string(corpus.get("path"), f"{path}: instances[{index}].path")
        if relative in by_file:
            fail(f"{path}: duplicate instance {relative}")
        expected = string(corpus.get("expected"), f"{path}: {relative}.expected")
        content_hash = string(
            corpus.get("content_hash"), f"{path}: {relative}.content_hash"
        )
        primary = string(instance.get("outcome"), f"{path}: {relative}.outcome")
        oracle = mapping(instance.get("oracle"), f"{path}: {relative}.oracle")
        oracle_outcome = string(
            oracle.get("outcome"), f"{path}: {relative}.oracle.outcome"
        )
        if primary not in ("sat", "unsat", "unknown"):
            fail(f"{path}: {relative}: invalid Axeyum outcome {primary!r}")
        if oracle_outcome not in ("sat", "unsat", "unknown"):
            fail(f"{path}: {relative}: invalid Z3 outcome {oracle_outcome!r}")
        if oracle.get("backend_kind") != "z3":
            fail(f"{path}: {relative}: oracle must be in-process z3")
        actual_population = population(primary, oracle_outcome)
        if oracle.get("decision_population") != actual_population:
            fail(f"{path}: {relative}: wrong decision population")
        if primary in ("sat", "unsat") and primary != expected:
            fail(f"{path}: {relative}: Axeyum disagrees with manifest")
        if oracle_outcome in ("sat", "unsat") and oracle_outcome != expected:
            fail(f"{path}: {relative}: Z3 disagrees with manifest")
        primary_ms = number(instance.get("cold_total_ms"), f"{path}: {relative}.cold")
        oracle_ms = number(oracle.get("cold_total_ms"), f"{path}: {relative}.z3.cold")
        if primary_ms < 0.0 or oracle_ms < 0.0:
            fail(f"{path}: {relative}: negative timing")
        counts[actual_population] += 1
        by_file[relative] = {
            "content_hash": content_hash,
            "expected": expected,
            "axeyum": primary,
            "z3": oracle_outcome,
            "axeyum_ms": primary_ms,
            "z3_ms": oracle_ms,
        }
    reported = mapping(
        oracle_summary.get("decision_population"),
        f"{path}: summary.oracle.decision_population",
    )
    key_map = {
        "both-decided": "both_decided",
        "axeyum-only-decided": "axeyum_only_decided",
        "z3-only-decided": "z3_only_decided",
        "neither-decided": "neither_decided",
    }
    for name, key in key_map.items():
        if integer(reported.get(key), f"{path}: population.{key}") != counts[name]:
            fail(f"{path}: summary population {key} does not match instances")
    if integer(reported.get("accounted"), f"{path}: population.accounted") != files:
        fail(f"{path}: decision populations do not account for every file")
    identity = {
        "manifest": mapping(config.get("corpus_manifest"), f"{path}: corpus_manifest"),
        "normalized_config": normalized_config(config),
        "environment_hash": string(
            mapping(config.get("experiment"), f"{path}: experiment").get(
                "environment_hash"
            ),
            f"{path}: environment_hash",
        ),
        "source_revision": string(
            mapping(
                mapping(config.get("experiment"), f"{path}: experiment").get("source"),
                f"{path}: source",
            ).get("revision"),
            f"{path}: source.revision",
        ),
    }
    return timeout, by_file, identity


def bootstrap_geomean(per_query_logs: Sequence[float]) -> dict[str, float | int]:
    if not per_query_logs:
        fail("paired fixed set is empty")
    point = math.exp(statistics.fmean(per_query_logs))
    generator = random.Random(0xA3E7_2026)
    samples = []
    for _ in range(10_000):
        samples.append(
            math.exp(
                statistics.fmean(
                    per_query_logs[generator.randrange(len(per_query_logs))]
                    for _ in per_query_logs
                )
            )
        )
    return {
        "queries": len(per_query_logs),
        "axeyum_over_z3_geomean": point,
        "bootstrap_seed": 0xA3E7_2026,
        "bootstrap_resamples": 10_000,
        "bootstrap_95_percent_ci_low": percentile(samples, 0.025),
        "bootstrap_95_percent_ci_high": percentile(samples, 0.975),
    }


def solver_stability(
    runs: Sequence[dict[str, dict[str, Any]]], solver: str
) -> dict[str, Any]:
    outcomes = {
        name: [run[name][solver] for run in runs]
        for name in sorted(runs[0])
    }
    drift = [name for name, values in outcomes.items() if len(set(values)) > 1]
    stable_decided = [
        name
        for name, values in outcomes.items()
        if len(set(values)) == 1 and values[0] in ("sat", "unsat")
    ]
    per_run = []
    for run in runs:
        counts = Counter(row[solver] for row in run.values())
        per_run.append({key: counts[key] for key in ("sat", "unsat", "unknown")})
    return {
        "per_repetition": per_run,
        "decided_count": distribution(
            [float(row["sat"] + row["unsat"]) for row in per_run]
        ),
        "unknown_count": distribution([float(row["unknown"]) for row in per_run]),
        "stable_decided_queries": len(stable_decided),
        "outcome_drift_queries": len(drift),
        "outcome_drift_paths": drift,
    }


def analyze_timeout(runs: Sequence[dict[str, dict[str, Any]]]) -> dict[str, Any]:
    axeyum = solver_stability(runs, "axeyum")
    z3 = solver_stability(runs, "z3")
    population_rows = []
    for run in runs:
        counts = Counter(population(row["axeyum"], row["z3"]) for row in run.values())
        population_rows.append({name: counts[name] for name in POPULATIONS})
    fixed = [
        name
        for name in sorted(runs[0])
        if all(
            run[name]["axeyum"] in ("sat", "unsat")
            and run[name]["z3"] in ("sat", "unsat")
            for run in runs
        )
    ]
    logs = []
    axeyum_ms = []
    z3_ms = []
    paired_axeyum_totals = []
    paired_z3_totals = []
    repetition_geomeans = []
    for name in fixed:
        query_logs = []
        for run in runs:
            left = run[name]["axeyum_ms"]
            right = run[name]["z3_ms"]
            if left <= 0.0 or right <= 0.0:
                fail(f"{name}: fixed-pair timing must be positive")
            query_logs.append(math.log(left / right))
            axeyum_ms.append(left)
            z3_ms.append(right)
        logs.append(statistics.fmean(query_logs))
    for run in runs:
        left = [run[name]["axeyum_ms"] for name in fixed]
        right = [run[name]["z3_ms"] for name in fixed]
        paired_axeyum_totals.append(sum(left))
        paired_z3_totals.append(sum(right))
        repetition_geomeans.append(
            math.exp(statistics.fmean(math.log(a / z) for a, z in zip(left, right)))
        )
    paired = bootstrap_geomean(logs)
    paired.update(
        {
            "observations": len(fixed) * len(runs),
            "query_boundary": "original parsed assertions for both in-process solvers",
            "selection": "queries both decided in every repetition at this timeout",
            "ratio_direction": "Axeyum/Z3; below 1 favors Axeyum",
            "axeyum_latency_ms": distribution(axeyum_ms),
            "z3_latency_ms": distribution(z3_ms),
            "per_repetition_axeyum_total_ms": distribution(paired_axeyum_totals),
            "per_repetition_z3_total_ms": distribution(paired_z3_totals),
            "per_repetition_axeyum_over_z3_geomean": distribution(
                repetition_geomeans
            ),
            "axeyum_cdf_ms": sorted(axeyum_ms),
            "z3_cdf_ms": sorted(z3_ms),
        }
    )
    return {
        "repetitions": len(runs),
        "axeyum": axeyum,
        "z3": z3,
        "decision_population_per_repetition": population_rows,
        "decision_population_count_variance": {
            name: distribution([float(row[name]) for row in population_rows])
            for name in POPULATIONS
        },
        "fixed_work_all_query_total_ms": {
            "axeyum": distribution(
                [sum(row["axeyum_ms"] for row in run.values()) for run in runs]
            ),
            "z3": distribution(
                [sum(row["z3_ms"] for row in run.values()) for run in runs]
            ),
            "interpretation": "descriptive fixed-work totals including timeout and nondecision costs; never a solved-only speed ratio",
        },
        "fixed_both_decided": paired,
    }


def validate_cvc5(
    report: dict[str, Any],
    timeouts: Sequence[int],
    repetitions: int,
    file_identity: dict[str, tuple[str, str]],
) -> tuple[dict[int, Any], dict[str, Any]]:
    if report.get("schema") != CVC5_SCHEMA:
        fail(f"cvc5 report schema must be {CVC5_SCHEMA}")
    if integer(report.get("measured_repetitions"), "cvc5.measured_repetitions") != repetitions:
        fail("cvc5 repetition count differs from Axeyum/Z3")
    reported_timeouts = [integer(value, "cvc5.timeouts_ms") for value in sequence(report.get("timeouts_ms"), "cvc5.timeouts_ms")]
    if reported_timeouts != list(timeouts):
        fail("cvc5 timeout tiers differ from Axeyum/Z3")
    manifest = mapping(report.get("manifest"), "cvc5.manifest")
    if integer(manifest.get("files"), "cvc5.manifest.files") != len(file_identity):
        fail("cvc5 manifest file count differs")
    rows_by_timeout: dict[int, list[dict[str, Any]]] = defaultdict(list)
    seen = set()
    verdicts: dict[str, set[str]] = defaultdict(set)
    for index, raw in enumerate(sequence(report.get("rows"), "cvc5.rows")):
        row = mapping(raw, f"cvc5.rows[{index}]")
        timeout = integer(row.get("timeout_ms"), f"cvc5.rows[{index}].timeout_ms")
        repetition = integer(row.get("repetition"), f"cvc5.rows[{index}].repetition")
        path = string(row.get("path"), f"cvc5.rows[{index}].path")
        key = (timeout, repetition, path)
        if key in seen:
            fail(f"duplicate cvc5 row {key}")
        seen.add(key)
        if path not in file_identity:
            fail(f"cvc5 row has unmanifested path {path}")
        content_hash, expected = file_identity[path]
        if row.get("content_hash") != content_hash or row.get("expected") != expected:
            fail(f"cvc5 row identity drift for {path}")
        outcome = string(row.get("outcome"), f"cvc5.rows[{index}].outcome")
        if outcome not in ("sat", "unsat", "unknown"):
            fail(f"invalid cvc5 outcome {outcome!r}")
        if outcome in ("sat", "unsat") and outcome != expected:
            fail(f"cvc5 disagrees with manifest for {path}")
        elapsed = integer(row.get("elapsed_nanos"), f"cvc5.rows[{index}].elapsed")
        if elapsed <= 0:
            fail(f"cvc5 elapsed time must be positive for {path}")
        rows_by_timeout[timeout].append(
            {"path": path, "repetition": repetition, "outcome": outcome, "elapsed_nanos": elapsed}
        )
        verdicts[path].add(outcome)
    expected_rows = len(file_identity) * repetitions * len(timeouts)
    if len(seen) != expected_rows:
        fail(f"cvc5 row cardinality must be {expected_rows}, got {len(seen)}")
    result = {}
    for timeout in timeouts:
        selected = rows_by_timeout[timeout]
        per_run = []
        for repetition in range(repetitions):
            run = [row for row in selected if row["repetition"] == repetition]
            if {row["path"] for row in run} != set(file_identity):
                fail(f"cvc5 timeout {timeout} repetition {repetition} membership drift")
            counts = Counter(row["outcome"] for row in run)
            per_run.append(
                {
                    "sat": counts["sat"],
                    "unsat": counts["unsat"],
                    "unknown": counts["unknown"],
                    "wall_time_s": sum(row["elapsed_nanos"] for row in run) / 1e9,
                }
            )
        drift = []
        stable_decided = 0
        for path in sorted(file_identity):
            outcomes = {
                row["outcome"] for row in selected if row["path"] == path
            }
            if len(outcomes) > 1:
                drift.append(path)
            elif next(iter(outcomes)) in ("sat", "unsat"):
                stable_decided += 1
        result[timeout] = {
            "per_repetition": per_run,
            "decided_count": distribution(
                [float(row["sat"] + row["unsat"]) for row in per_run]
            ),
            "unknown_count": distribution([float(row["unknown"]) for row in per_run]),
            "wall_time_s": distribution([row["wall_time_s"] for row in per_run]),
            "stable_decided_queries": stable_decided,
            "outcome_drift_queries": len(drift),
            "outcome_drift_paths": drift,
        }
    return result, {
        "manifest": manifest,
        "solver": mapping(report.get("cvc5"), "cvc5.cvc5"),
        "all_timeout_outcomes": verdicts,
    }


def analyze(
    axeyum_paths: Sequence[Path],
    cvc5_path: Path,
    required_timeouts: Sequence[int] = DEFAULT_TIMEOUTS,
) -> dict[str, Any]:
    grouped: dict[int, list[dict[str, dict[str, Any]]]] = defaultdict(list)
    artifact_records = []
    source_versions: set[int] = set()
    reference_identity = None
    file_identity = None
    all_verdicts: dict[str, set[str]] = defaultdict(set)
    for path in axeyum_paths:
        artifact, digest = load_json(path)
        source_versions.add(integer(artifact.get("version"), f"{path}: version"))
        timeout, instances, identity = validate_axeyum_artifact(artifact, path)
        if timeout not in required_timeouts:
            fail(f"{path}: undeclared timeout {timeout}")
        current_files = {
            name: (row["content_hash"], row["expected"])
            for name, row in instances.items()
        }
        if reference_identity is None:
            reference_identity = identity
            file_identity = current_files
        elif identity != reference_identity:
            fail(f"{path}: configuration, environment, source, or manifest identity drift")
        elif current_files != file_identity:
            fail(f"{path}: instance identity drift")
        grouped[timeout].append(instances)
        artifact_records.append(
            {
                "path": path.name,
                "sha256": digest,
                "timeout_ms": timeout,
                "artifact_version": integer(artifact.get("version"), f"{path}: version"),
            }
        )
        for name, row in instances.items():
            all_verdicts[name].update((row["axeyum"], row["z3"]))
    if sorted(grouped) != list(required_timeouts):
        fail(f"Axeyum/Z3 timeout tiers must be {list(required_timeouts)}")
    repetitions = {len(grouped[timeout]) for timeout in required_timeouts}
    if len(repetitions) != 1 or next(iter(repetitions)) < MIN_REPETITIONS:
        fail("every timeout must have the same N>=5 repetitions")
    repetition_count = next(iter(repetitions))
    assert reference_identity is not None and file_identity is not None

    cvc5_report, cvc5_digest = load_json(cvc5_path)
    cvc5_results, cvc5_identity = validate_cvc5(
        cvc5_report,
        required_timeouts,
        repetition_count,
        file_identity,
    )
    if cvc5_identity["manifest"].get("content_hash") != reference_identity["manifest"].get("content_hash"):
        fail("cvc5 and Axeyum/Z3 manifest hashes differ")
    for name, outcomes in cvc5_identity.pop("all_timeout_outcomes").items():
        all_verdicts[name].update(outcomes)
    contradictions = {
        name: sorted(outcomes)
        for name, outcomes in all_verdicts.items()
        if "sat" in outcomes and "unsat" in outcomes
    }
    if contradictions:
        first = next(iter(contradictions.items()))
        fail(f"cross-solver SAT/UNSAT contradiction: {first}")

    return {
        "schema": ANALYSIS_SCHEMA,
        "source_artifact_version": (
            next(iter(source_versions)) if len(source_versions) == 1 else None
        ),
        "source_artifact_versions": sorted(source_versions),
        "contract": {
            "timeouts_ms": list(required_timeouts),
            "repetitions": repetition_count,
            "fixed_work": "same hash-bound manifest files at every timeout and repetition",
            "verdict_gate": "all decided outcomes must match the manifest; SAT/UNSAT contradiction across any solver, timeout, or repetition fails",
            "unknown_policy": "Unknown is a reported nondecision, never agreement or error",
            "timing_policy": "Axeyum/Z3 paired ratios use only queries both decided in every repetition at a timeout; cvc5 subprocess wall time is not divided into that ratio",
        },
        "identity": {
            "manifest": reference_identity["manifest"],
            "environment_hash": reference_identity["environment_hash"],
            "source_revision": reference_identity["source_revision"],
            "files": len(file_identity),
            "cvc5": cvc5_identity,
        },
        "inputs": {
            "axeyum_z3_artifacts": sorted(
                artifact_records, key=lambda row: (row["timeout_ms"], row["path"])
            ),
            "cvc5_artifact": {"path": cvc5_path.name, "sha256": cvc5_digest},
        },
        "cross_solver_sat_unsat_contradictions": 0,
        "timeouts": {
            str(timeout): {
                "axeyum_z3": analyze_timeout(grouped[timeout]),
                "cvc5": cvc5_results[timeout],
            }
            for timeout in required_timeouts
        },
    }


def atomic_write(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=path.parent, delete=False
    ) as handle:
        json.dump(value, handle, indent=2, sort_keys=True)
        handle.write("\n")
        temporary = Path(handle.name)
    temporary.replace(path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cvc5", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("artifacts", nargs="+", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        result = analyze(args.artifacts, args.cvc5)
        atomic_write(args.out, result)
    except AnalysisError as error:
        raise SystemExit(f"timeout-sweep analysis failed: {error}") from error
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
