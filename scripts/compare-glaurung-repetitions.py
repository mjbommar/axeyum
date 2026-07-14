#!/usr/bin/env python3
"""Compare two validated Glaurung repetition summaries across source commits.

The corpus, solver settings, toolchain, and hardware must be identical. The
only permitted configuration difference is the clean Axeyum source revision.
The output reports raw Axeyum and Z3 changes, their ratio change, per-stage
changes, and optional explicit regression gates.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import math
import os
import re
import statistics
import tempfile
from pathlib import Path
from types import ModuleType
from typing import Any, NoReturn, Sequence


REPETITION_SUMMARY_VERSION = 1
SOURCE_ARTIFACT_VERSION = 21
COMPARISON_VERSION = 1
STAGE_KEYS = (
    "word_preprocess_s",
    "bit_blast_s",
    "cnf_encode_s",
    "cnf_inprocess_s",
    "solve_s",
    "model_lift_s",
    "model_replay_s",
)
SHA256_PATTERN = re.compile(r"sha256:[0-9a-f]{64}\Z")
REVISION_PATTERN = re.compile(r"[0-9a-f]{40}\Z")


def load_summarizer() -> ModuleType:
    path = Path(__file__).with_name("summarize-glaurung-repetitions.py")
    spec = importlib.util.spec_from_file_location(
        "axeyum_glaurung_repetition_summary", path
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"load repetition summarizer module from {path}")
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


def require_bool(value: Any, location: str) -> bool:
    if not isinstance(value, bool):
        fail(f"{location} must be a boolean")
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


def require_sha256(value: Any, location: str) -> str:
    result = require_string(value, location)
    if SHA256_PATTERN.fullmatch(result) is None:
        fail(f"{location} must be `sha256:` plus 64 lowercase hexadecimal digits")
    return result


def require_revision(value: Any, location: str) -> str:
    result = require_string(value, location)
    if REVISION_PATTERN.fullmatch(result) is None:
        fail(f"{location} must be a 40-digit lowercase hexadecimal Git revision")
    return result


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
    return require_mapping(value, str(path)), "sha256:" + hashlib.sha256(
        data
    ).hexdigest()


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
            standard_deviation / mean * 100.0 if mean != 0.0 else 0.0
        ),
    }


def validate_distribution(value: Any, samples: Sequence[float], location: str) -> None:
    actual = require_mapping(value, location)
    expected = distribution(samples)
    if set(actual) != set(expected):
        fail(f"{location} fields do not match repetition-summary schema v1")
    for key, expected_value in expected.items():
        actual_value = require_number(actual.get(key), f"{location}.{key}")
        if not math.isclose(actual_value, expected_value, rel_tol=1e-12, abs_tol=1e-15):
            fail(f"{location}.{key} does not match the source runs")


def validate_config_identity(
    summary: dict[str, Any], path: Path
) -> tuple[dict[str, Any], dict[str, str]]:
    config = require_mapping(summary.get("config"), f"{path}: config")
    if not require_bool(
        config.get("require_reproducible_run"),
        f"{path}: config.require_reproducible_run",
    ):
        fail(f"{path}: config.require_reproducible_run must be true")
    if require_int(config.get("jobs"), f"{path}: config.jobs") != 1:
        fail(f"{path}: config.jobs must be 1")
    if not require_bool(config.get("compare_z3"), f"{path}: config.compare_z3"):
        fail(f"{path}: config.compare_z3 must be true")
    if not require_bool(
        config.get("require_in_process_z3"), f"{path}: config.require_in_process_z3"
    ):
        fail(f"{path}: config.require_in_process_z3 must be true")
    if require_bool(config.get("prove_unsat"), f"{path}: config.prove_unsat"):
        fail(f"{path}: proof-companion timings are not client-performance summaries")
    if (
        require_string(config.get("backend_kind"), f"{path}: config.backend_kind")
        != "sat-bv"
    ):
        fail(f"{path}: config.backend_kind must be `sat-bv`")
    if require_string(config.get("logic"), f"{path}: config.logic") != "QF_BV":
        fail(f"{path}: config.logic must be `QF_BV`")
    if not require_bool(config.get("preprocess"), f"{path}: config.preprocess"):
        fail(f"{path}: config.preprocess must be true")
    if not math.isclose(
        require_number(
            config.get("min_decided_percent"), f"{path}: config.min_decided_percent"
        ),
        100.0,
        rel_tol=0.0,
        abs_tol=1e-12,
    ):
        fail(f"{path}: config.min_decided_percent must be 100")
    identity = require_mapping(summary.get("identity"), f"{path}: identity")
    experiment = require_mapping(config.get("experiment"), f"{path}: config.experiment")
    source = require_mapping(
        experiment.get("source"), f"{path}: config.experiment.source"
    )
    if require_bool(source.get("dirty"), f"{path}: config.experiment.source.dirty"):
        fail(f"{path}: source must be clean")
    manifest = require_mapping(
        config.get("corpus_manifest"), f"{path}: config.corpus_manifest"
    )
    expected = {
        "config_hash": require_string(
            config.get("config_hash"), f"{path}: config.config_hash"
        ),
        "corpus_hash": require_string(
            config.get("corpus_hash"), f"{path}: config.corpus_hash"
        ),
        "manifest_hash": require_sha256(
            manifest.get("content_hash"), f"{path}: config.corpus_manifest.content_hash"
        ),
        "environment_hash": require_sha256(
            experiment.get("environment_hash"),
            f"{path}: config.experiment.environment_hash",
        ),
        "source_revision": require_revision(
            source.get("revision"), f"{path}: config.experiment.source.revision"
        ),
        "backend": require_string(config.get("backend"), f"{path}: config.backend"),
        "compare_backend": require_string(
            config.get("compare_backend"), f"{path}: config.compare_backend"
        ),
    }
    for key, expected_value in expected.items():
        location = f"{path}: identity.{key}"
        actual = (
            require_revision(identity.get(key), location)
            if key == "source_revision"
            else require_sha256(identity.get(key), location)
            if key in {"manifest_hash", "environment_hash"}
            else require_string(identity.get(key), location)
        )
        if actual != expected_value:
            fail(f"{location} does not match config")
    return config, expected


def validate_repetition_summary(
    value: dict[str, Any], path: Path
) -> tuple[dict[str, Any], dict[str, str], list[dict[str, Any]]]:
    version = require_int(value.get("version"), f"{path}: version")
    if version != REPETITION_SUMMARY_VERSION:
        fail(
            f"{path}: repetition summary version {version} is unsupported; expected "
            f"{REPETITION_SUMMARY_VERSION}"
        )
    source_version = require_int(
        value.get("source_artifact_version"), f"{path}: source_artifact_version"
    )
    if source_version != SOURCE_ARTIFACT_VERSION:
        fail(
            f"{path}: source artifact version {source_version} is unsupported; expected "
            f"{SOURCE_ARTIFACT_VERSION}"
        )
    repetitions = require_int(value.get("repetitions"), f"{path}: repetitions")
    if repetitions < 2:
        fail(f"{path}: repetitions must be at least 2")
    config, identity = validate_config_identity(value, path)
    raw_runs = require_list(value.get("runs"), f"{path}: runs")
    if len(raw_runs) != repetitions:
        fail(f"{path}: runs length must equal repetitions")

    summary_root = path.parent.resolve()
    source_artifacts: list[Path] = []
    for index, raw_run in enumerate(raw_runs):
        run = require_mapping(raw_run, f"{path}: runs[{index}]")
        artifact = require_string(
            run.get("artifact"), f"{path}: runs[{index}].artifact"
        )
        valid_segments = (
            not artifact.startswith("/")
            and "\\" not in artifact
            and all(segment not in {"", ".", ".."} for segment in artifact.split("/"))
        )
        if not valid_segments:
            fail(f"{path}: runs[{index}].artifact must be a normalized relative path")
        source = (summary_root / artifact).resolve()
        try:
            source.relative_to(summary_root)
        except ValueError:
            fail(f"{path}: runs[{index}].artifact escapes the summary directory")
        source_artifacts.append(source)
    try:
        recomputed = SUMMARIZER.summarize(source_artifacts)
    except SUMMARIZER.SummaryError as error:
        fail(f"{path}: source artifact validation failed: {error}")
    if recomputed != value:
        fail(f"{path}: repetition summary does not match its source artifacts")

    runs: list[dict[str, Any]] = []
    artifact_paths: set[str] = set()
    expected_files: int | None = None
    for index, raw_run in enumerate(raw_runs, start=1):
        location = f"{path}: runs[{index - 1}]"
        run = require_mapping(raw_run, location)
        if require_int(run.get("repetition"), f"{location}.repetition") != index:
            fail(f"{location}.repetition must be {index}")
        artifact_path = require_string(run.get("artifact"), f"{location}.artifact")
        if Path(artifact_path).is_absolute() or artifact_path in artifact_paths:
            fail(f"{location}.artifact must be a unique relative path")
        artifact_paths.add(artifact_path)
        require_sha256(
            run.get("artifact_content_hash"), f"{location}.artifact_content_hash"
        )
        files = require_int(run.get("files"), f"{location}.files")
        if files <= 0:
            fail(f"{location}.files must be positive")
        if expected_files is None:
            expected_files = files
        elif files != expected_files:
            fail(f"{location}.files differs from the first trial")
        axeyum = require_number(run.get("axeyum_total_s"), f"{location}.axeyum_total_s")
        z3 = require_number(run.get("z3_total_s"), f"{location}.z3_total_s")
        ratio = require_number(
            run.get("axeyum_over_z3_ratio"), f"{location}.axeyum_over_z3_ratio"
        )
        if axeyum < 0.0 or z3 <= 0.0:
            fail(f"{location} requires Axeyum >= 0 and Z3 > 0")
        if not math.isclose(ratio, axeyum / z3, rel_tol=1e-12, abs_tol=1e-15):
            fail(f"{location}.axeyum_over_z3_ratio does not match totals")
        raw_stages = require_mapping(run.get("stages"), f"{location}.stages")
        stages = {
            key: require_number(raw_stages.get(key), f"{location}.stages.{key}")
            for key in STAGE_KEYS
        }
        if any(stage < 0.0 for stage in stages.values()):
            fail(f"{location}.stages must be non-negative")
        if not math.isclose(sum(stages.values()), axeyum, rel_tol=1e-9, abs_tol=1e-12):
            fail(f"{location}.stages do not sum to axeyum_total_s")
        runs.append(
            {
                "axeyum_total_s": axeyum,
                "z3_total_s": z3,
                "axeyum_over_z3_ratio": ratio,
                "stages": stages,
            }
        )

    assert expected_files is not None
    selected_entries = require_int(
        require_mapping(
            config.get("corpus_manifest"), f"{path}: config.corpus_manifest"
        ).get("selected_entries"),
        f"{path}: config.corpus_manifest.selected_entries",
    )
    if selected_entries != expected_files:
        fail(f"{path}: selected manifest entries must equal each trial's files")

    variance = require_mapping(value.get("variance"), f"{path}: variance")
    for key in ("axeyum_total_s", "z3_total_s", "axeyum_over_z3_ratio"):
        validate_distribution(
            variance.get(key), [run[key] for run in runs], f"{path}: variance.{key}"
        )
    stage_variance = require_mapping(
        variance.get("stages_s"), f"{path}: variance.stages_s"
    )
    if set(stage_variance) != set(STAGE_KEYS):
        fail(
            f"{path}: variance.stages_s fields do not match repetition-summary schema v1"
        )
    for key in STAGE_KEYS:
        validate_distribution(
            stage_variance.get(key),
            [run["stages"][key] for run in runs],
            f"{path}: variance.stages_s.{key}",
        )
    return config, identity, runs


def normalized_config(config: dict[str, Any]) -> dict[str, Any]:
    normalized = copy.deepcopy(config)
    require_mapping(
        require_mapping(normalized.get("experiment"), "config.experiment").get(
            "source"
        ),
        "config.experiment.source",
    ).pop("revision", None)
    return normalized


def metric_comparison(
    baseline: Sequence[float], candidate: Sequence[float], *, lower_is_better: bool
) -> dict[str, Any]:
    baseline_mean = statistics.fmean(baseline)
    candidate_mean = statistics.fmean(candidate)
    delta = candidate_mean - baseline_mean
    delta_percent = delta / baseline_mean * 100.0 if baseline_mean != 0.0 else None
    baseline_variance = statistics.variance(baseline) if len(baseline) > 1 else 0.0
    candidate_variance = statistics.variance(candidate) if len(candidate) > 1 else 0.0
    standard_error = math.sqrt(
        baseline_variance / len(baseline) + candidate_variance / len(candidate)
    )
    standardized_delta = delta / standard_error if standard_error != 0.0 else None
    if delta == 0.0:
        direction = "unchanged"
    elif lower_is_better:
        direction = "improvement" if delta < 0.0 else "regression"
    else:
        direction = "lower" if delta < 0.0 else "higher"
    return {
        "baseline": distribution(baseline),
        "candidate": distribution(candidate),
        "candidate_minus_baseline": delta,
        "candidate_minus_baseline_percent": delta_percent,
        "combined_standard_error": standard_error,
        "standardized_delta": standardized_delta,
        "direction": direction,
        "lower_is_better": lower_is_better,
    }


def gate_record(
    ratio: dict[str, Any],
    axeyum: dict[str, Any],
    z3: dict[str, Any],
    max_ratio_regression_percent: float | None,
    max_axeyum_regression_percent: float | None,
    max_z3_drift_percent: float | None,
) -> dict[str, Any]:
    checks: list[dict[str, Any]] = []

    def add_regression_check(
        name: str, metric: dict[str, Any], threshold: float | None
    ) -> None:
        if threshold is None:
            return
        delta = metric["candidate_minus_baseline_percent"]
        assert delta is not None
        observed = max(0.0, delta)
        checks.append(
            {
                "name": name,
                "kind": "maximum positive regression percent",
                "threshold_percent": threshold,
                "observed_percent": observed,
                "passed": observed <= threshold,
            }
        )

    add_regression_check("axeyum_over_z3_ratio", ratio, max_ratio_regression_percent)
    add_regression_check("axeyum_total_s", axeyum, max_axeyum_regression_percent)
    if max_z3_drift_percent is not None:
        delta = z3["candidate_minus_baseline_percent"]
        assert delta is not None
        checks.append(
            {
                "name": "z3_total_s",
                "kind": "maximum absolute control drift percent",
                "threshold_percent": max_z3_drift_percent,
                "observed_percent": abs(delta),
                "passed": abs(delta) <= max_z3_drift_percent,
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
    max_z3_drift_percent: float | None = None,
) -> dict[str, Any]:
    baseline_path = baseline_path.resolve()
    candidate_path = candidate_path.resolve()
    if baseline_path == candidate_path:
        fail("baseline and candidate repetition summaries must be different files")
    baseline_value, baseline_hash = load_json(baseline_path)
    candidate_value, candidate_hash = load_json(candidate_path)
    baseline_config, baseline_identity, baseline_runs = validate_repetition_summary(
        baseline_value, baseline_path
    )
    candidate_config, candidate_identity, candidate_runs = validate_repetition_summary(
        candidate_value, candidate_path
    )
    if baseline_identity["source_revision"] == candidate_identity["source_revision"]:
        fail("baseline and candidate must identify different clean source revisions")
    if normalized_config(baseline_config) != normalized_config(candidate_config):
        fail(
            "baseline and candidate configurations differ beyond the permitted source revision"
        )

    common_parent = Path(
        os.path.commonpath([str(baseline_path.parent), str(candidate_path.parent)])
    )
    axeyum = metric_comparison(
        [run["axeyum_total_s"] for run in baseline_runs],
        [run["axeyum_total_s"] for run in candidate_runs],
        lower_is_better=True,
    )
    z3 = metric_comparison(
        [run["z3_total_s"] for run in baseline_runs],
        [run["z3_total_s"] for run in candidate_runs],
        lower_is_better=False,
    )
    ratio = metric_comparison(
        [run["axeyum_over_z3_ratio"] for run in baseline_runs],
        [run["axeyum_over_z3_ratio"] for run in candidate_runs],
        lower_is_better=True,
    )
    stages = {
        key: metric_comparison(
            [run["stages"][key] for run in baseline_runs],
            [run["stages"][key] for run in candidate_runs],
            lower_is_better=True,
        )
        for key in STAGE_KEYS
    }
    return {
        "version": COMPARISON_VERSION,
        "repetition_summary_version": REPETITION_SUMMARY_VERSION,
        "source_artifact_version": SOURCE_ARTIFACT_VERSION,
        "contract": {
            "identity": "same corpus/config/toolchain/hardware/backends; only clean source revision may differ",
            "interpretation": "raw Axeyum and Z3 controls accompany the ratio; standardized_delta is descriptive, not a significance claim",
            "gate": "thresholds are explicit caller policy; no synthetic default is promoted",
        },
        "comparison_identity": {
            key: baseline_identity[key]
            for key in (
                "config_hash",
                "corpus_hash",
                "manifest_hash",
                "environment_hash",
                "backend",
                "compare_backend",
            )
        },
        "baseline": {
            "summary": baseline_path.relative_to(common_parent).as_posix(),
            "summary_content_hash": baseline_hash,
            "source_revision": baseline_identity["source_revision"],
            "repetitions": len(baseline_runs),
        },
        "candidate": {
            "summary": candidate_path.relative_to(common_parent).as_posix(),
            "summary_content_hash": candidate_hash,
            "source_revision": candidate_identity["source_revision"],
            "repetitions": len(candidate_runs),
        },
        "metrics": {
            "axeyum_total_s": axeyum,
            "z3_total_s": z3,
            "axeyum_over_z3_ratio": ratio,
            "stages_s": stages,
        },
        "gate": gate_record(
            ratio,
            axeyum,
            z3,
            max_ratio_regression_percent,
            max_axeyum_regression_percent,
            max_z3_drift_percent,
        ),
    }


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


def non_negative_float(value: str) -> float:
    try:
        parsed = float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError(str(error)) from error
    if not math.isfinite(parsed) or parsed < 0.0:
        raise argparse.ArgumentTypeError("threshold must be a finite number >= 0")
    return parsed


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--max-ratio-regression-percent", type=non_negative_float)
    parser.add_argument("--max-axeyum-regression-percent", type=non_negative_float)
    parser.add_argument("--max-z3-drift-percent", type=non_negative_float)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    output = args.out.resolve()
    inputs = {args.baseline.resolve(), args.candidate.resolve()}
    if output in inputs:
        print(
            "comparison output must not overwrite an input summary", file=os.sys.stderr
        )
        return 1
    try:
        result = compare(
            args.baseline,
            args.candidate,
            max_ratio_regression_percent=args.max_ratio_regression_percent,
            max_axeyum_regression_percent=args.max_axeyum_regression_percent,
            max_z3_drift_percent=args.max_z3_drift_percent,
        )
        write_json_atomic(output, result)
    except ComparisonError as error:
        try:
            output.unlink(missing_ok=True)
        except OSError as remove_error:
            print(f"remove stale {output}: {remove_error}", file=os.sys.stderr)
        print(error, file=os.sys.stderr)
        return 1
    if not result["gate"]["passed"]:
        failed = ", ".join(
            check["name"] for check in result["gate"]["checks"] if not check["passed"]
        )
        print(f"benchmark regression gate failed: {failed}", file=os.sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
