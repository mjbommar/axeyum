#!/usr/bin/env python3
"""Compare validated Glaurung full-shard repetitions across clean commits."""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import math
import os
import statistics
import tempfile
from pathlib import Path
from types import ModuleType
from typing import Any, NoReturn, Sequence


SOURCE_SCHEMA = "axeyum-glaurung-qfbv-sharded-repetitions-v1"
COMPARISON_SCHEMA = "axeyum-glaurung-qfbv-sharded-comparison-v1"
STAGE_KEYS = (
    "word_preprocess_s",
    "bit_blast_s",
    "cnf_encode_s",
    "cnf_inprocess_s",
    "solve_s",
    "model_lift_s",
    "model_replay_s",
)


def load_summarizer() -> ModuleType:
    path = Path(__file__).with_name("summarize-glaurung-shard-repetitions.py")
    spec = importlib.util.spec_from_file_location(
        "axeyum_glaurung_shard_repetitions", path
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"load shard repetition summarizer from {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


SUMMARIZER = load_summarizer()


class ComparisonError(ValueError):
    """A repetition summary is invalid or the pair is not comparable."""


def fail(message: str) -> NoReturn:
    raise ComparisonError(message)


def require_mapping(value: Any, location: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{location} must be a JSON object")
    return value


def require_list(value: Any, location: str) -> list[Any]:
    if not isinstance(value, list):
        fail(f"{location} must be a JSON array")
    return value


def require_int(value: Any, location: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        fail(f"{location} must be an integer")
    return value


def require_number(value: Any, location: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        fail(f"{location} must be a number")
    result = float(value)
    if not math.isfinite(result):
        fail(f"{location} must be finite")
    return result


def require_string(value: Any, location: str) -> str:
    if not isinstance(value, str) or not value:
        fail(f"{location} must be a non-empty string")
    return value


def load_json(path: Path) -> tuple[dict[str, Any], str]:
    try:
        data = path.read_bytes()
    except OSError as error:
        fail(f"read {path}: {error}")
    try:
        value = json.loads(
            data,
            parse_constant=lambda token: fail(
                f"parse {path}: non-finite JSON number {token}"
            ),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"parse {path}: {error}")
    return require_mapping(value, str(path)), "sha256:" + hashlib.sha256(data).hexdigest()


def validate_summary(
    value: dict[str, Any], path: Path
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    if value.get("schema") != SOURCE_SCHEMA:
        fail(f"{path}: schema must be {SOURCE_SCHEMA}")
    raw_runs = require_list(value.get("runs"), f"{path}: runs")
    repetitions = require_int(value.get("repetitions"), f"{path}: repetitions")
    if repetitions < 2 or len(raw_runs) != repetitions:
        fail(f"{path}: at least two runs and an exact repetition count are required")
    source_paths = [
        Path(require_string(run.get("summary"), f"{path}: runs[{index}].summary"))
        for index, run in enumerate(raw_runs)
        if isinstance(run, dict)
    ]
    if len(source_paths) != repetitions:
        fail(f"{path}: every run must be an object with a source summary")
    try:
        recomputed = SUMMARIZER.summarize(source_paths)
    except SUMMARIZER.SummaryError as error:
        fail(f"{path}: source composite validation failed: {error}")
    if recomputed != value:
        fail(f"{path}: repetition summary does not match its source composites")
    runs = []
    for index, raw_run in enumerate(raw_runs):
        location = f"{path}: runs[{index}]"
        run = require_mapping(raw_run, location)
        stages_raw = require_mapping(run.get("stages"), f"{location}.stages")
        runs.append(
            {
                "axeyum_total_s": require_number(
                    run.get("axeyum_total_s"), f"{location}.axeyum_total_s"
                ),
                "z3_total_s": require_number(
                    run.get("z3_total_s"), f"{location}.z3_total_s"
                ),
                "axeyum_over_z3_ratio": require_number(
                    run.get("axeyum_over_z3_ratio"),
                    f"{location}.axeyum_over_z3_ratio",
                ),
                "maximum_resident_set_kib": require_number(
                    run.get("maximum_resident_set_kib"),
                    f"{location}.maximum_resident_set_kib",
                ),
                "stages": {
                    key: require_number(stages_raw.get(key), f"{location}.stages.{key}")
                    for key in STAGE_KEYS
                },
            }
        )
    return require_mapping(value.get("identity"), f"{path}: identity"), runs


def source_revision(identity: dict[str, Any], location: str) -> str:
    source = require_mapping(identity.get("source"), f"{location}.source")
    return require_string(source.get("source_revision"), f"{location}.source_revision")


def comparable_identity(identity: dict[str, Any], location: str) -> dict[str, Any]:
    result = copy.deepcopy(identity)
    source = require_mapping(result.get("source"), f"{location}.source")
    if source.get("dirty") != "false" or source.get("reproducible") != "true":
        fail(f"{location}: source must be clean and reproducible")
    source.pop("source_revision", None)
    source.pop("normalized_config_sha256", None)
    config = require_mapping(
        result.get("normalized_config"), f"{location}.normalized_config"
    )
    experiment = require_mapping(config.get("experiment"), f"{location}.experiment")
    config_source = require_mapping(
        experiment.get("source"), f"{location}.experiment.source"
    )
    config_source.pop("revision", None)
    # Deterministic work is validated within each revision but may legitimately
    # change when an optimization changes the AIG/CNF construction.
    result.pop("deterministic_work", None)
    return result


def distribution(values: Sequence[float]) -> dict[str, float]:
    ordered = sorted(values)

    def percentile(percent: int) -> float:
        rank = max(0, math.ceil(percent * len(ordered) / 100) - 1)
        return ordered[min(rank, len(ordered) - 1)]

    mean = statistics.fmean(ordered)
    standard_deviation = statistics.stdev(ordered) if len(ordered) > 1 else 0.0
    return {
        "min": ordered[0],
        "p50": percentile(50),
        "p95": percentile(95),
        "max": ordered[-1],
        "mean": mean,
        "sample_standard_deviation": standard_deviation,
        "coefficient_of_variation_percent": (
            standard_deviation / mean * 100 if mean != 0 else 0.0
        ),
    }


def metric_comparison(
    baseline: Sequence[float], candidate: Sequence[float]
) -> dict[str, Any]:
    baseline_mean = statistics.fmean(baseline)
    candidate_mean = statistics.fmean(candidate)
    delta = candidate_mean - baseline_mean
    percent = delta / baseline_mean * 100 if baseline_mean != 0 else None
    return {
        "baseline": distribution(baseline),
        "candidate": distribution(candidate),
        "candidate_minus_baseline": delta,
        "candidate_minus_baseline_percent": percent,
        "direction": "unchanged" if delta == 0 else "improvement" if delta < 0 else "regression",
        "lower_is_better": True,
    }


def gate(
    metrics: dict[str, dict[str, Any]],
    *,
    max_ratio_regression_percent: float | None,
    max_axeyum_regression_percent: float | None,
    max_rss_regression_percent: float | None,
    max_z3_drift_percent: float | None,
) -> dict[str, Any]:
    checks = []
    for name, threshold in (
        ("axeyum_over_z3_ratio", max_ratio_regression_percent),
        ("axeyum_total_s", max_axeyum_regression_percent),
        ("maximum_resident_set_kib", max_rss_regression_percent),
    ):
        if threshold is not None:
            observed = max(0.0, metrics[name]["candidate_minus_baseline_percent"])
            checks.append(
                {
                    "name": name,
                    "kind": "maximum positive regression percent",
                    "threshold_percent": threshold,
                    "observed_percent": observed,
                    "passed": observed <= threshold,
                }
            )
    if max_z3_drift_percent is not None:
        observed = abs(metrics["z3_total_s"]["candidate_minus_baseline_percent"])
        checks.append(
            {
                "name": "z3_total_s",
                "kind": "maximum absolute control drift percent",
                "threshold_percent": max_z3_drift_percent,
                "observed_percent": observed,
                "passed": observed <= max_z3_drift_percent,
            }
        )
    return {
        "configured": bool(checks),
        "passed": all(check["passed"] for check in checks),
        "checks": checks,
    }


def compare(
    baseline_path: Path,
    candidate_path: Path,
    *,
    max_ratio_regression_percent: float | None = None,
    max_axeyum_regression_percent: float | None = None,
    max_rss_regression_percent: float | None = None,
    max_z3_drift_percent: float | None = None,
) -> dict[str, Any]:
    baseline_path = baseline_path.resolve()
    candidate_path = candidate_path.resolve()
    if baseline_path == candidate_path:
        fail("baseline and candidate summaries must be different files")
    baseline_value, baseline_hash = load_json(baseline_path)
    candidate_value, candidate_hash = load_json(candidate_path)
    if baseline_value.get("policy") != candidate_value.get("policy"):
        fail("baseline and candidate policies must match")
    baseline_identity, baseline_runs = validate_summary(baseline_value, baseline_path)
    candidate_identity, candidate_runs = validate_summary(candidate_value, candidate_path)
    baseline_revision = source_revision(baseline_identity, "baseline identity")
    candidate_revision = source_revision(candidate_identity, "candidate identity")
    if baseline_revision == candidate_revision:
        fail("baseline and candidate must identify different clean source revisions")
    if comparable_identity(baseline_identity, "baseline identity") != comparable_identity(
        candidate_identity, "candidate identity"
    ):
        fail("baseline and candidate corpus, environment, or configuration differs")

    metric_names = (
        "axeyum_total_s",
        "z3_total_s",
        "axeyum_over_z3_ratio",
        "maximum_resident_set_kib",
    )
    metrics = {
        name: metric_comparison(
            [run[name] for run in baseline_runs],
            [run[name] for run in candidate_runs],
        )
        for name in metric_names
    }
    stages = {
        key: metric_comparison(
            [run["stages"][key] for run in baseline_runs],
            [run["stages"][key] for run in candidate_runs],
        )
        for key in STAGE_KEYS
    }
    gates = gate(
        metrics,
        max_ratio_regression_percent=max_ratio_regression_percent,
        max_axeyum_regression_percent=max_axeyum_regression_percent,
        max_rss_regression_percent=max_rss_regression_percent,
        max_z3_drift_percent=max_z3_drift_percent,
    )
    return {
        "schema": COMPARISON_SCHEMA,
        "policy": baseline_value["policy"],
        "contract": {
            "identity": "capture, environment, toolchain, solver policy, and resource configuration match; only clean source revision and deterministic construction work may change",
            "controls": "raw Axeyum, Z3, normalized ratio, maximum child RSS, and every attributed stage remain visible",
            "gate": "thresholds are explicit same-environment policy, evaluated only after exact identity/source validation",
        },
        "baseline": {
            "summary": str(baseline_path),
            "summary_content_hash": baseline_hash,
            "source_revision": baseline_revision,
            "repetitions": len(baseline_runs),
        },
        "candidate": {
            "summary": str(candidate_path),
            "summary_content_hash": candidate_hash,
            "source_revision": candidate_revision,
            "repetitions": len(candidate_runs),
        },
        "metrics": metrics | {"stages_s": stages},
        "gate": gates,
    }


def nonnegative_optional(value: str) -> float:
    result = float(value)
    if not math.isfinite(result) or result < 0:
        raise argparse.ArgumentTypeError("threshold must be a finite non-negative number")
    return result


def write_json_atomic(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    rendered = json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + "\n"
    temporary: str | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            dir=path.parent,
            prefix=f".{path.name}.",
            delete=False,
        ) as handle:
            temporary = handle.name
            handle.write(rendered)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    except OSError as error:
        if temporary is not None:
            try:
                os.unlink(temporary)
            except OSError:
                pass
        fail(f"write {path}: {error}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--max-ratio-regression-percent", type=nonnegative_optional)
    parser.add_argument("--max-axeyum-regression-percent", type=nonnegative_optional)
    parser.add_argument("--max-rss-regression-percent", type=nonnegative_optional)
    parser.add_argument("--max-z3-drift-percent", type=nonnegative_optional)
    parser.add_argument("--out", required=True, type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    output = args.out.resolve()
    try:
        result = compare(
            args.baseline,
            args.candidate,
            max_ratio_regression_percent=args.max_ratio_regression_percent,
            max_axeyum_regression_percent=args.max_axeyum_regression_percent,
            max_rss_regression_percent=args.max_rss_regression_percent,
            max_z3_drift_percent=args.max_z3_drift_percent,
        )
        write_json_atomic(output, result)
        if result["gate"]["configured"] and not result["gate"]["passed"]:
            return 2
    except ComparisonError as error:
        try:
            output.unlink(missing_ok=True)
        except OSError as remove_error:
            print(f"remove stale {output}: {remove_error}", file=os.sys.stderr)
        print(error, file=os.sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
