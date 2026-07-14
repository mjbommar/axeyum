#!/usr/bin/env python3
"""Validate and summarize repeated Glaurung QF_BV benchmark artifacts.

Each input must be an independently launched artifact-v23 run from the strict
single-worker Glaurung recipe. The script fails closed on identity drift or any
acceptance-gate failure, then reports whole-corpus variance. It intentionally
does not merge per-query records: keeping repetitions as separate processes and
artifacts preserves the cold-run boundary and bounds summarizer memory.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import statistics
import tempfile
from pathlib import Path
from typing import Any, NoReturn, Sequence


SOURCE_ARTIFACT_VERSION = 24
REPETITION_SUMMARY_VERSION = 1
STAGE_KEYS = (
    "word_preprocess_s",
    "bit_blast_s",
    "cnf_encode_s",
    "cnf_inprocess_s",
    "solve_s",
    "model_lift_s",
    "model_replay_s",
)


class SummaryError(ValueError):
    """An input artifact violates the repeated-run evidence contract."""


def fail(message: str) -> NoReturn:
    raise SummaryError(message)


def require_mapping(value: Any, location: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{location} must be a JSON object")
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


def require_zero(value: Any, location: str) -> None:
    if require_int(value, location) != 0:
        fail(f"{location} must be zero")


def require_count(value: Any, expected: int, location: str) -> None:
    actual = require_int(value, location)
    if actual != expected:
        fail(f"{location} must be {expected}, got {actual}")


def load_artifact(path: Path) -> tuple[dict[str, Any], str]:
    try:
        data = path.read_bytes()
    except OSError as error:
        fail(f"read {path}: {error}")
    try:
        artifact = json.loads(
            data,
            parse_constant=lambda value: fail(
                f"parse {path}: non-finite JSON number {value}"
            ),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"parse {path}: {error}")
    return require_mapping(artifact, str(path)), "sha256:" + hashlib.sha256(
        data
    ).hexdigest()


def validate_identity(config: dict[str, Any], path: Path) -> dict[str, str]:
    prefix = f"{path}: config"
    if not require_bool(
        config.get("require_reproducible_run"), f"{prefix}.require_reproducible_run"
    ):
        fail(f"{prefix}.require_reproducible_run must be true")
    if require_int(config.get("jobs"), f"{prefix}.jobs") != 1:
        fail(f"{prefix}.jobs must be 1 for cold-stage attribution")
    if not require_bool(config.get("compare_z3"), f"{prefix}.compare_z3"):
        fail(f"{prefix}.compare_z3 must be true")
    if not require_bool(
        config.get("require_in_process_z3"), f"{prefix}.require_in_process_z3"
    ):
        fail(f"{prefix}.require_in_process_z3 must be true")
    validate_determinism(config.get("determinism"), f"{prefix}.determinism")
    if not require_bool(
        config.get("require_deterministic_resources"),
        f"{prefix}.require_deterministic_resources",
    ):
        fail(f"{prefix}.require_deterministic_resources must be true")
    validate_resource_profile(config.get("resources"), config, f"{prefix}.resources")

    experiment = require_mapping(config.get("experiment"), f"{prefix}.experiment")
    source = require_mapping(experiment.get("source"), f"{prefix}.experiment.source")
    if require_bool(source.get("dirty"), f"{prefix}.experiment.source.dirty"):
        fail(f"{prefix}.experiment.source.dirty must be false")
    manifest = require_mapping(
        config.get("corpus_manifest"), f"{prefix}.corpus_manifest"
    )
    return {
        "config_hash": require_string(
            config.get("config_hash"), f"{prefix}.config_hash"
        ),
        "corpus_hash": require_string(
            config.get("corpus_hash"), f"{prefix}.corpus_hash"
        ),
        "manifest_hash": require_string(
            manifest.get("content_hash"), f"{prefix}.corpus_manifest.content_hash"
        ),
        "environment_hash": require_string(
            experiment.get("environment_hash"), f"{prefix}.experiment.environment_hash"
        ),
        "source_revision": require_string(
            source.get("revision"), f"{prefix}.experiment.source.revision"
        ),
        "backend": require_string(config.get("backend"), f"{prefix}.backend"),
        "compare_backend": require_string(
            config.get("compare_backend"), f"{prefix}.compare_backend"
        ),
    }


def validate_determinism(value: Any, location: str) -> None:
    profile = require_mapping(value, location)
    if profile.get("profile") != "axeyum-bench-fixed-seeds-v1":
        fail(f"{location}.profile must be `axeyum-bench-fixed-seeds-v1`")
    expected_order = (
        "stable manifest order (or deterministic lexical path order without a manifest)"
    )
    if profile.get("corpus_order") != expected_order:
        fail(f"{location}.corpus_order does not match the v1 profile")
    sat_bv = require_mapping(profile.get("sat_bv"), f"{location}.sat_bv")
    if sat_bv.get("adapter") != "rustsat-batsat":
        fail(f"{location}.sat_bv.adapter must be `rustsat-batsat`")
    expected_source = (
        "batsat::SolverOpts::default from the Cargo.lock-pinned dependency"
    )
    if sat_bv.get("option_source") != expected_source:
        fail(f"{location}.sat_bv.option_source does not match the v1 profile")
    expected_numbers = {
        "random_seed": 91_648_253.0,
        "random_var_freq": 0.0,
    }
    for key, expected in expected_numbers.items():
        actual = require_number(sat_bv.get(key), f"{location}.sat_bv.{key}")
        if actual != expected:
            fail(f"{location}.sat_bv.{key} must be {expected}")
    for key in ("random_polarity", "random_initial_activity"):
        if require_bool(sat_bv.get(key), f"{location}.sat_bv.{key}"):
            fail(f"{location}.sat_bv.{key} must be false")
    z3 = require_mapping(profile.get("z3"), f"{location}.z3")
    if require_int(z3.get("random_seed"), f"{location}.z3.random_seed") != 0:
        fail(f"{location}.z3.random_seed must be 0")
    if z3.get("parameter") != "random_seed":
        fail(f"{location}.z3.parameter must be `random_seed`")
    if not require_bool(z3.get("set_explicitly"), f"{location}.z3.set_explicitly"):
        fail(f"{location}.z3.set_explicitly must be true")


def validate_resource_profile(
    value: Any, config: dict[str, Any], location: str
) -> None:
    profile = require_mapping(value, location)
    if profile.get("profile") != "axeyum-qfbv-cold-bounded-v1":
        fail(f"{location}.profile must be `axeyum-qfbv-cold-bounded-v1`")
    if not require_bool(profile.get("required"), f"{location}.required"):
        fail(f"{location}.required must be true")
    limits = require_mapping(profile.get("limits"), f"{location}.limits")
    mappings = {
        "search": "resource_limit",
        "dag_nodes": "node_budget",
        "cnf_variables": "cnf_variable_budget",
        "cnf_clauses": "cnf_clause_budget",
    }
    for profile_key, config_key in mappings.items():
        limit = require_int(limits.get(profile_key), f"{location}.limits.{profile_key}")
        if limit <= 0:
            fail(f"{location}.limits.{profile_key} must be positive")
        if require_int(config.get(config_key), f"config.{config_key}") != limit:
            fail(f"{location}.limits.{profile_key} must match config.{config_key}")
    units = require_mapping(profile.get("units"), f"{location}.units")
    if units.get("primary_search") != "rustsat-batsat within_budget progress checks":
        fail(f"{location}.units.primary_search does not match the v1 profile")
    if units.get("z3_oracle_search") != "Z3 rlimit units":
        fail(f"{location}.units.z3_oracle_search does not match the v1 profile")
    timeout = require_int(
        profile.get("wall_clock_safety_timeout_ms"),
        f"{location}.wall_clock_safety_timeout_ms",
    )
    if timeout <= 0 or timeout != require_int(
        config.get("timeout_ms"), "config.timeout_ms"
    ):
        fail(
            f"{location}.wall_clock_safety_timeout_ms must be positive and match config"
        )
    if require_bool(
        profile.get("wall_clock_is_deterministic"),
        f"{location}.wall_clock_is_deterministic",
    ):
        fail(f"{location}.wall_clock_is_deterministic must be false")
    if require_bool(
        profile.get("cross_backend_numeric_limits_are_work_equivalent"),
        f"{location}.cross_backend_numeric_limits_are_work_equivalent",
    ):
        fail(
            f"{location}.cross_backend_numeric_limits_are_work_equivalent must be false"
        )


def validate_summary(
    summary: dict[str, Any], config: dict[str, Any], path: Path
) -> dict[str, Any]:
    prefix = f"{path}: summary"
    files = require_int(summary.get("files"), f"{prefix}.files")
    if files <= 0:
        fail(f"{prefix}.files must be positive")
    require_count(summary.get("decided"), files, f"{prefix}.decided")
    decided_percent = require_number(
        summary.get("decided_percent"), f"{prefix}.decided_percent"
    )
    if not math.isclose(decided_percent, 100.0, rel_tol=0.0, abs_tol=1e-12):
        fail(f"{prefix}.decided_percent must be 100")
    for field in ("errors", "disagree", "model_replay_failures"):
        require_zero(summary.get(field), f"{prefix}.{field}")

    manifest = require_mapping(summary.get("manifest"), f"{prefix}.manifest")
    require_count(manifest.get("expected"), files, f"{prefix}.manifest.expected")
    require_count(manifest.get("compared"), files, f"{prefix}.manifest.compared")
    require_count(manifest.get("agree"), files, f"{prefix}.manifest.agree")
    require_zero(manifest.get("disagree"), f"{prefix}.manifest.disagree")

    oracle = require_mapping(summary.get("oracle"), f"{prefix}.oracle")
    if not require_bool(oracle.get("enabled"), f"{prefix}.oracle.enabled"):
        fail(f"{prefix}.oracle.enabled must be true")
    require_count(oracle.get("compared"), files, f"{prefix}.oracle.compared")
    require_count(oracle.get("agree"), files, f"{prefix}.oracle.agree")
    require_zero(oracle.get("disagree"), f"{prefix}.oracle.disagree")
    require_zero(oracle.get("skipped"), f"{prefix}.oracle.skipped")

    proof = require_mapping(
        summary.get("unsat_proof_replay"), f"{prefix}.unsat_proof_replay"
    )
    if require_bool(proof.get("requested"), f"{prefix}.unsat_proof_replay.requested"):
        require_zero(proof.get("missing"), f"{prefix}.unsat_proof_replay.missing")

    layers = require_mapping(
        summary.get("layer_attribution"), f"{prefix}.layer_attribution"
    )
    require_count(
        layers.get("instances"), files, f"{prefix}.layer_attribution.instances"
    )
    stage_seconds = {
        key: require_number(layers.get(key), f"{prefix}.layer_attribution.{key}")
        for key in STAGE_KEYS
    }
    if any(value < 0.0 for value in stage_seconds.values()):
        fail(f"{prefix}.layer_attribution stage totals must be non-negative")
    pipeline_seconds = require_number(
        layers.get("total_pipeline_s"), f"{prefix}.layer_attribution.total_pipeline_s"
    )
    if not math.isclose(
        sum(stage_seconds.values()), pipeline_seconds, rel_tol=1e-9, abs_tol=1e-12
    ):
        fail(f"{prefix}.layer_attribution stage totals do not sum to total_pipeline_s")

    comparison = require_mapping(
        summary.get("client_comparison"), f"{prefix}.client_comparison"
    )
    require_count(
        comparison.get("instances"), files, f"{prefix}.client_comparison.instances"
    )
    axeyum_seconds = require_number(
        comparison.get("axeyum_total_s"), f"{prefix}.client_comparison.axeyum_total_s"
    )
    z3_seconds = require_number(
        comparison.get("z3_total_s"), f"{prefix}.client_comparison.z3_total_s"
    )
    if axeyum_seconds < 0.0 or z3_seconds <= 0.0:
        fail(f"{prefix}.client_comparison totals require Axeyum >= 0 and Z3 > 0")
    if not math.isclose(axeyum_seconds, pipeline_seconds, rel_tol=1e-9, abs_tol=1e-12):
        fail(f"{prefix} Axeyum client total must equal attributed pipeline total")
    ratio = require_number(
        comparison.get("axeyum_over_z3_ratio"),
        f"{prefix}.client_comparison.axeyum_over_z3_ratio",
    )
    if not math.isclose(
        ratio, axeyum_seconds / z3_seconds, rel_tol=1e-9, abs_tol=1e-12
    ):
        fail(f"{prefix}.client_comparison ratio does not match its totals")

    selected_entries = require_int(
        require_mapping(config.get("corpus_manifest"), "config.corpus_manifest").get(
            "selected_entries"
        ),
        "config.corpus_manifest.selected_entries",
    )
    if selected_entries != files:
        fail(f"{path}: selected manifest entries must equal summary.files")
    return {
        "files": files,
        "axeyum_total_s": axeyum_seconds,
        "z3_total_s": z3_seconds,
        "axeyum_over_z3_ratio": ratio,
        "stages": stage_seconds,
    }


def distribution(values: Sequence[float]) -> dict[str, float]:
    ordered = sorted(values)

    def percentile(percent: int) -> float:
        rank = max(0, math.ceil(percent * len(ordered) / 100) - 1)
        return ordered[min(rank, len(ordered) - 1)]

    mean = statistics.fmean(ordered)
    sample_standard_deviation = statistics.stdev(ordered) if len(ordered) > 1 else 0.0
    return {
        "min": ordered[0],
        "p50": percentile(50),
        "p95": percentile(95),
        "max": ordered[-1],
        "mean": mean,
        "sample_standard_deviation": sample_standard_deviation,
        "coefficient_of_variation_percent": (
            sample_standard_deviation / mean * 100.0 if mean != 0.0 else 0.0
        ),
    }


def summarize(paths: Sequence[Path]) -> dict[str, Any]:
    ordered_paths = sorted(
        (path.resolve() for path in paths), key=lambda path: str(path)
    )
    if len(ordered_paths) < 2:
        fail(
            "at least two independently produced artifacts are required to report variance"
        )
    if len(set(ordered_paths)) != len(ordered_paths):
        fail("input artifact paths must be unique")
    common_parent = Path(
        os.path.commonpath([str(path.parent) for path in ordered_paths])
    )

    expected_config: dict[str, Any] | None = None
    identity: dict[str, str] | None = None
    runs: list[dict[str, Any]] = []
    for index, path in enumerate(ordered_paths, start=1):
        artifact, artifact_hash = load_artifact(path)
        version = require_int(artifact.get("version"), f"{path}: version")
        if version != SOURCE_ARTIFACT_VERSION:
            fail(
                f"{path}: artifact version {version} is unsupported; expected "
                f"{SOURCE_ARTIFACT_VERSION}"
            )
        config = require_mapping(artifact.get("config"), f"{path}: config")
        current_identity = validate_identity(config, path)
        if expected_config is None:
            expected_config = config
            identity = current_identity
        elif config != expected_config:
            fail(f"{path}: config differs from the first repetition")
        summary = validate_summary(
            require_mapping(artifact.get("summary"), f"{path}: summary"), config, path
        )
        runs.append(
            {
                "repetition": index,
                "artifact": path.relative_to(common_parent).as_posix(),
                "artifact_content_hash": artifact_hash,
                **summary,
            }
        )

    assert expected_config is not None and identity is not None
    return {
        "version": REPETITION_SUMMARY_VERSION,
        "source_artifact_version": SOURCE_ARTIFACT_VERSION,
        "contract": {
            "run_boundary": "independent process per whole-corpus cold trial",
            "identity": "every source artifact has byte-identical config and a clean reproducible-run identity",
            "acceptance": "every trial is 100% decided with zero errors, disagreements, oracle gaps, and replay failures",
            "statistics": "nearest-rank p50/p95 and sample standard deviation across whole-corpus trials",
            "artifact_paths": "relative to the directory shared by summary.json and all source artifacts",
        },
        "identity": identity,
        "config": expected_config,
        "repetitions": len(runs),
        "runs": runs,
        "variance": {
            "axeyum_total_s": distribution([run["axeyum_total_s"] for run in runs]),
            "z3_total_s": distribution([run["z3_total_s"] for run in runs]),
            "axeyum_over_z3_ratio": distribution(
                [run["axeyum_over_z3_ratio"] for run in runs]
            ),
            "stages_s": {
                key: distribution([run["stages"][key] for run in runs])
                for key in STAGE_KEYS
            },
        },
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


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifacts", nargs="+", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    return parser.parse_args()


def validate_output_location(output: Path, inputs: Sequence[Path]) -> None:
    input_parents = [path.parent.resolve() for path in inputs]
    common_parent = Path(os.path.commonpath([str(parent) for parent in input_parents]))
    if output.parent.resolve() != common_parent:
        fail(
            "repetition summary output must be in the common source-artifact directory "
            "so recorded relative paths remain self-contained"
        )


def main() -> int:
    args = parse_args()
    output = args.out.resolve()
    inputs = [path.resolve() for path in args.artifacts]
    if output in inputs:
        print(
            "repetition summary output must not overwrite an input artifact",
            file=os.sys.stderr,
        )
        return 1
    try:
        validate_output_location(output, inputs)
        write_json_atomic(output, summarize(inputs))
    except SummaryError as error:
        # A failed refresh must not leave a previously valid-looking summary at
        # the requested output path. Source artifacts are never touched.
        try:
            output.unlink(missing_ok=True)
        except OSError as remove_error:
            print(f"remove stale {output}: {remove_error}", file=os.sys.stderr)
        print(error, file=os.sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
