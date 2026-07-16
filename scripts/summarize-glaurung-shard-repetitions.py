#!/usr/bin/env python3
"""Validate repeated complete Glaurung shard summaries and report variance."""

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


SOURCE_SCHEMA = "axeyum-glaurung-qfbv-sharded-summary-v1"
SUMMARY_SCHEMA = "axeyum-glaurung-qfbv-sharded-repetitions-v1"
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
    """A composite summary violates the repetition evidence contract."""


def fail(message: str) -> NoReturn:
    raise SummaryError(message)


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


def validate_aggregate(
    aggregate: dict[str, Any], capture: dict[str, Any], path: Path
) -> dict[str, Any]:
    location = f"{path}: aggregate"
    if not require_bool(aggregate.get("publication_ready"), f"{location}.publication_ready"):
        fail(f"{location}.publication_ready must be true")
    files = require_int(aggregate.get("files"), f"{location}.files")
    if files != require_int(capture.get("files"), f"{path}: capture.files"):
        fail(f"{location}.files must match capture.files")
    sat = require_int(aggregate.get("sat"), f"{location}.sat")
    unsat = require_int(aggregate.get("unsat"), f"{location}.unsat")
    if sat < 0 or unsat < 0 or sat + unsat != files:
        fail(f"{location}: sat + unsat must equal files")
    axeyum = require_number(aggregate.get("axeyum_total_s"), f"{location}.axeyum_total_s")
    z3 = require_number(aggregate.get("z3_total_s"), f"{location}.z3_total_s")
    ratio = require_number(
        aggregate.get("axeyum_over_z3_ratio"), f"{location}.axeyum_over_z3_ratio"
    )
    if axeyum < 0 or z3 <= 0 or not math.isclose(
        ratio, axeyum / z3, rel_tol=1e-9, abs_tol=1e-12
    ):
        fail(f"{location}: client totals or ratio are inconsistent")
    stages_raw = require_mapping(aggregate.get("stages"), f"{location}.stages")
    stages = {
        key: require_number(stages_raw.get(key), f"{location}.stages.{key}")
        for key in STAGE_KEYS
    }
    if any(value < 0 for value in stages.values()) or not math.isclose(
        sum(stages.values()), axeyum, rel_tol=1e-9, abs_tol=1e-12
    ):
        fail(f"{location}: stage totals must be non-negative and sum to Axeyum total")
    rewrite = require_mapping(aggregate.get("rewrite"), f"{location}.rewrite")
    for field in ("decision_changes", "sat_unsat_conflicts"):
        if require_int(rewrite.get(field), f"{location}.rewrite.{field}") != 0:
            fail(f"{location}.rewrite.{field} must be zero")
    rss = require_int(
        aggregate.get("maximum_resident_set_kib"),
        f"{location}.maximum_resident_set_kib",
    )
    if rss <= 0 or rss > 4 * 1024 * 1024:
        fail(f"{location}.maximum_resident_set_kib must be within 4 GiB")
    return {
        "files": files,
        "sat": sat,
        "unsat": unsat,
        "axeyum_total_s": axeyum,
        "z3_total_s": z3,
        "axeyum_over_z3_ratio": ratio,
        "maximum_resident_set_kib": rss,
        "stages": stages,
    }


def invariant_projection(summary: dict[str, Any], path: Path) -> dict[str, Any]:
    aggregate = require_mapping(summary.get("aggregate"), f"{path}: aggregate")
    shards = require_list(summary.get("shards"), f"{path}: shards")
    shard_invariants = []
    for index, raw_shard in enumerate(shards):
        location = f"{path}: shards[{index}]"
        shard = require_mapping(raw_shard, location)
        shard_invariants.append(
            {
                key: shard.get(key)
                for key in (
                    "index",
                    "tier",
                    "files",
                    "manifest_sha256",
                    "capture_index_sha256",
                    "sat",
                    "unsat",
                    "rewrite",
                    "construction",
                    "exit_status",
                )
            }
        )
    return {
        "source_artifact_version": summary.get("source_artifact_version"),
        "policy": summary.get("policy"),
        "contract": summary.get("contract"),
        "capture": summary.get("capture"),
        "identity": summary.get("identity"),
        "normalized_config": summary.get("normalized_config"),
        "outcomes": {
            "files": aggregate.get("files"),
            "sat": aggregate.get("sat"),
            "unsat": aggregate.get("unsat"),
        },
        "rewrite": aggregate.get("rewrite"),
        "construction": aggregate.get("construction"),
        "shards": shard_invariants,
    }


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
            standard_deviation / mean * 100.0 if mean != 0 else 0.0
        ),
    }


def summarize(paths: Sequence[Path]) -> dict[str, Any]:
    resolved = sorted((path.resolve() for path in paths), key=str)
    if len(resolved) < 2:
        fail("at least two complete composite summaries are required")
    if len(set(resolved)) != len(resolved):
        fail("composite summary paths must be unique")
    expected_invariants: dict[str, Any] | None = None
    policy: str | None = None
    runs: list[dict[str, Any]] = []
    for index, path in enumerate(resolved, start=1):
        summary, content_hash = load_json(path)
        if summary.get("schema") != SOURCE_SCHEMA:
            fail(f"{path}: schema must be {SOURCE_SCHEMA}")
        current_policy = require_string(summary.get("policy"), f"{path}: policy")
        if current_policy not in {"raw", "canonical"}:
            fail(f"{path}: unsupported policy {current_policy}")
        capture = require_mapping(summary.get("capture"), f"{path}: capture")
        aggregate = validate_aggregate(
            require_mapping(summary.get("aggregate"), f"{path}: aggregate"),
            capture,
            path,
        )
        invariants = invariant_projection(summary, path)
        if expected_invariants is None:
            expected_invariants = invariants
            policy = current_policy
        elif invariants != expected_invariants:
            fail(f"{path}: composite identity, coverage, or deterministic work differs")
        runs.append(
            {
                "repetition": index,
                "summary": str(path),
                "summary_content_hash": content_hash,
                **aggregate,
            }
        )
    assert expected_invariants is not None and policy is not None
    return {
        "schema": SUMMARY_SCHEMA,
        "source_schema": SOURCE_SCHEMA,
        "policy": policy,
        "contract": {
            "unit": "one complete validated shard-set composite per repetition",
            "identity": "capture, source, normalized configuration, deterministic work, outcomes, and shard membership are exact across repetitions",
            "statistics": "nearest-rank p50/p95 and sample standard deviation over complete composites",
            "warning": "individual child shards are never statistical repetitions",
        },
        "identity": {
            "capture": expected_invariants["capture"],
            "source": expected_invariants["identity"],
            "normalized_config": expected_invariants["normalized_config"],
            "deterministic_work": {
                "outcomes": expected_invariants["outcomes"],
                "rewrite": expected_invariants["rewrite"],
                "construction": expected_invariants["construction"],
                "shards": expected_invariants["shards"],
            },
        },
        "repetitions": len(runs),
        "runs": runs,
        "variance": {
            key: distribution([run[key] for run in runs])
            for key in (
                "axeyum_total_s",
                "z3_total_s",
                "axeyum_over_z3_ratio",
                "maximum_resident_set_kib",
            )
        }
        | {
            "stages_s": {
                key: distribution([run["stages"][key] for run in runs])
                for key in STAGE_KEYS
            }
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
    parser.add_argument("summaries", nargs="+", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    output = args.out.resolve()
    inputs = [path.resolve() for path in args.summaries]
    if output in inputs:
        print("output must not overwrite an input summary", file=os.sys.stderr)
        return 1
    try:
        write_json_atomic(output, summarize(inputs))
    except SummaryError as error:
        try:
            output.unlink(missing_ok=True)
        except OSError as remove_error:
            print(f"remove stale {output}: {remove_error}", file=os.sys.stderr)
        print(error, file=os.sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
