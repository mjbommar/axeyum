#!/usr/bin/env python3
"""Fail-closed paired analysis for repeated Glaurung ordered traces.

The publication scalar is the geometric mean of per-occurrence Z3/Axeyum
latency ratios. An occurrence enters that population only when both backends
decide it in every fixed-work repetition. V3 additionally reports the nine
registered Z3/Axeyum/Bitwuzla cold/warm contrasts and an all-six acceptance
gate. V4 preserves those contrasts while validating backend-specific
deterministic limits and typed stop reasons. Ratio-of-sums is never reported.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import pathlib
import random
import re
import statistics
import sys
from dataclasses import dataclass
from typing import Any, Sequence


TRACE_SCHEMA = "glaurung-ordered-trace-v1"
MEASUREMENT_SCHEMA_V1 = "glaurung-ordered-check-measurement-v1"
MEASUREMENT_SCHEMA_V2 = "glaurung-ordered-check-measurement-v2"
MEASUREMENT_SCHEMA_V3 = "glaurung-ordered-check-measurement-v3"
MEASUREMENT_SCHEMA_V4 = "glaurung-ordered-check-measurement-v4"
MEASUREMENT_SCHEMAS = {
    MEASUREMENT_SCHEMA_V1,
    MEASUREMENT_SCHEMA_V2,
    MEASUREMENT_SCHEMA_V3,
    MEASUREMENT_SCHEMA_V4,
}
FAIR_CELLS_V2 = ("z3_cold", "z3_warm", "axeyum_cold", "axeyum_warm")
FAIR_CELLS_V3 = FAIR_CELLS_V2 + ("bitwuzla_cold", "bitwuzla_warm")
FAIR_MEASUREMENT_SCHEMAS = {
    MEASUREMENT_SCHEMA_V2,
    MEASUREMENT_SCHEMA_V3,
    MEASUREMENT_SCHEMA_V4,
}
NEUTRAL_MEASUREMENT_SCHEMAS = {MEASUREMENT_SCHEMA_V3, MEASUREMENT_SCHEMA_V4}
RESOURCE_SPECS = {
    "z3_cold": ("z3", "z3-rlimit"),
    "z3_warm": ("z3", "z3-rlimit"),
    "axeyum_cold": ("axeyum", "axeyum-progress-checks"),
    "axeyum_warm": ("axeyum", "axeyum-progress-checks"),
    "bitwuzla_cold": ("bitwuzla", "bitwuzla-termination-polls"),
    "bitwuzla_warm": ("bitwuzla", "bitwuzla-termination-polls"),
}
STOP_REASONS = {None, "resource-limit", "wall-timeout", "other"}
DECIDED = {"sat", "unsat"}
OUTCOMES = DECIDED | {"unknown", "error", "no-solver"}
EXECUTION_CLASSES = {
    "cold-one-shot",
    "warm-snapshot",
    "warm-created",
    "warm-retained",
    "warm-timeout-cold-retry",
    "fallback-missing-path",
    "fallback-auto-probe",
    "fallback-path-cap",
    "fallback-assertion-cap",
    "invalid-direct-delta",
}
PURE_WARM_CLASSES = {"warm-snapshot", "warm-created", "warm-retained"}
DIRECT_WARM_CLASSES = {"warm-created", "warm-retained"}
NEUTRAL_WARM_CLASSES = DIRECT_WARM_CLASSES | {
    "fallback-missing-delta",
    "invalid-direct-delta",
}
OUTPUT_CONFIGURATION_KEYS = {
    "GLAURUNG_AXEYUM_PROFILE_DIR",
    "GLAURUNG_DUMP_QUERIES",
    "GLAURUNG_ORDERED_TRACE_DIR",
    "GLAURUNG_SHADOW_SPLIT_DIR",
}


class AnalysisError(ValueError):
    """The trace set cannot support a paired publication statistic."""


@dataclass(frozen=True)
class Check:
    identity: tuple[Any, ...]
    check_id: str
    query_sha256: str
    purpose: str
    active_constraint_count: int
    z3_outcome: str
    axeyum_outcome: str
    z3_nanos: int
    axeyum_nanos: int
    axeyum_execution: str
    z3_cold_outcome: str | None = None
    z3_warm_outcome: str | None = None
    axeyum_cold_outcome: str | None = None
    axeyum_warm_outcome: str | None = None
    z3_cold_nanos: int | None = None
    z3_warm_nanos: int | None = None
    axeyum_cold_nanos: int | None = None
    axeyum_warm_nanos: int | None = None
    z3_warm_execution: str | None = None
    axeyum_warm_execution: str | None = None
    bitwuzla_cold_outcome: str | None = None
    bitwuzla_warm_outcome: str | None = None
    bitwuzla_cold_nanos: int | None = None
    bitwuzla_warm_nanos: int | None = None
    bitwuzla_warm_execution: str | None = None
    resource_counters: dict[str, dict[str, Any]] | None = None


@dataclass(frozen=True)
class Trace:
    path: pathlib.Path
    driver_label: str
    driver_sha256: str
    configuration_identity: str
    measurement_schema: str
    checks: tuple[Check, ...]


def fail(message: str) -> None:
    raise AnalysisError(message)


def load_json(path: pathlib.Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"cannot read {path}: {error}")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def stable_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def require_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        fail(f"{label} is not a nonempty string")
    return value


def require_positive_int(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        fail(f"{label} is not a positive integer")
    return value


def configuration_identity(manifest: dict[str, Any]) -> str:
    configuration = manifest.get("analysis_configuration")
    if not isinstance(configuration, dict):
        fail("manifest analysis_configuration is not an object")
    normalized_configuration = {
        key: value
        for key, value in configuration.items()
        if key not in OUTPUT_CONFIGURATION_KEYS
    }
    identity = {
        "schema": manifest.get("schema"),
        "version": manifest.get("version"),
        "check_measurement_schema": manifest.get("check_measurement_schema"),
        "source": manifest.get("source"),
        "driver_sha256": manifest.get("driver", {}).get("sha256")
        if isinstance(manifest.get("driver"), dict)
        else None,
        "analysis_command": manifest.get("analysis_command"),
        "analysis_configuration": normalized_configuration,
        "solver_features": manifest.get("solver_features"),
        "trusted_oracle": manifest.get("trusted_oracle"),
        "toolchain": manifest.get("toolchain"),
        "host_identity": manifest.get("host_identity"),
        "worker_count": manifest.get("worker_count"),
    }
    if manifest.get("check_measurement_schema") in NEUTRAL_MEASUREMENT_SCHEMAS:
        identity["neutral_measurement_backend"] = manifest.get(
            "neutral_measurement_backend"
        )
    if manifest.get("check_measurement_schema") == MEASUREMENT_SCHEMA_V4:
        identity["solver_work_budgets"] = manifest.get("solver_work_budgets")
    return stable_json(identity)


def validate_neutral_backend_identity(manifest: dict[str, Any]) -> None:
    identity = manifest.get("neutral_measurement_backend")
    if identity != {
        "backend": "bitwuzla",
        "runtime_version": "0.9.1",
        "authoritative_in_shadow_mode": False,
        "role": "benchmark-only-neutral",
    }:
        fail("invalid v3 neutral measurement backend identity")


def validate_work_budget_manifest(manifest: dict[str, Any]) -> dict[str, Any]:
    budgets = manifest.get("solver_work_budgets")
    if not isinstance(budgets, dict):
        fail("v4 manifest lacks solver_work_budgets")
    if budgets.get("cross_backend_unit_equivalence") is not False:
        fail("v4 work-budget units must not claim cross-backend equivalence")
    require_positive_int(budgets.get("wall_safety_cap_ms"), "wall safety cap")
    for backend, unit in (
        ("z3", "z3-rlimit"),
        ("axeyum", "axeyum-progress-checks"),
        ("bitwuzla", "bitwuzla-termination-polls"),
    ):
        entry = budgets.get(backend)
        if not isinstance(entry, dict) or entry.get("unit") != unit:
            fail(f"invalid v4 {backend} work-budget unit")
        require_positive_int(entry.get("limit"), f"{backend} work-budget limit")
    return budgets


def validate_resource_counters(
    event: dict[str, Any],
    fair_values: dict[str, Any],
    budgets: dict[str, Any],
    check_id: str,
    root: pathlib.Path,
) -> dict[str, dict[str, Any]]:
    counters = event.get("resource_counters")
    if not isinstance(counters, dict) or set(counters) != set(RESOURCE_SPECS):
        fail(f"invalid v4 resource counters for {check_id} in {root}")
    normalized: dict[str, dict[str, Any]] = {}
    for cell, (backend, unit) in RESOURCE_SPECS.items():
        entry = counters.get(cell)
        expected_limit = budgets[backend]["limit"]
        if (
            not isinstance(entry, dict)
            or entry.get("unit") != unit
            or entry.get("limit") != expected_limit
        ):
            fail(f"invalid v4 {cell} resource identity for {check_id} in {root}")
        reason = entry.get("stop_reason")
        if reason not in STOP_REASONS:
            fail(f"invalid v4 {cell} stop reason for {check_id} in {root}")
        outcome = fair_values[f"{cell}_outcome"]
        if (outcome == "unknown") != (reason is not None):
            fail(f"v4 {cell} outcome/stop-reason mismatch for {check_id} in {root}")
        normalized[cell] = {
            "unit": unit,
            "limit": expected_limit,
            "stop_reason": reason,
        }
    return normalized


def verify_query_artifacts(
    root: pathlib.Path, manifest: dict[str, Any], referenced_hashes: set[str]
) -> None:
    index_path = root / "query-index-v1.json"
    try:
        index_bytes = index_path.read_bytes()
    except OSError as error:
        fail(f"cannot read {index_path}: {error}")
    if sha256(index_bytes) != manifest.get("query_index_sha256"):
        fail(f"query-index SHA-256 mismatch in {root}")
    try:
        index = json.loads(index_bytes)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"invalid query index in {root}: {error}")
    if not isinstance(index, dict) or index.get("version") != 1:
        fail(f"invalid query index schema in {root}")
    entries = index.get("queries")
    if not isinstance(entries, list):
        fail(f"query index has no query list in {root}")

    indexed_hashes: set[str] = set()
    for entry in entries:
        if not isinstance(entry, dict):
            fail(f"query index entry is not an object in {root}")
        content_hash = require_string(entry.get("content_hash"), "query content hash")
        if not re.fullmatch(r"[0-9a-f]{64}", content_hash):
            fail(f"invalid query content hash in {root}")
        if content_hash in indexed_hashes:
            fail(f"duplicate query content hash {content_hash} in {root}")
        indexed_hashes.add(content_hash)
        expected_relative_path = f"queries/{content_hash}.smt2"
        if entry.get("path") != expected_relative_path:
            fail(f"noncanonical query path for {content_hash} in {root}")
        query_path = root / expected_relative_path
        try:
            query_bytes = query_path.read_bytes()
        except OSError as error:
            fail(f"cannot read {query_path}: {error}")
        if sha256(query_bytes) != content_hash:
            fail(f"query content SHA-256 mismatch for {content_hash} in {root}")

    if indexed_hashes != referenced_hashes:
        fail(f"query index/check reference mismatch in {root}")
    if manifest.get("query_count") != len(indexed_hashes):
        fail(f"manifest query count mismatch in {root}")


def load_trace(root: pathlib.Path) -> Trace:
    manifest_path = root / "trace-manifest-v1.json"
    events_path = root / "events-v1.ndjson"
    manifest = load_json(manifest_path)
    if not isinstance(manifest, dict):
        fail(f"{manifest_path} is not an object")
    if manifest.get("schema") != TRACE_SCHEMA or manifest.get("version") != 1:
        fail(f"{root} is not an ordered trace v1")
    measurement_schema = manifest.get("check_measurement_schema")
    if measurement_schema not in MEASUREMENT_SCHEMAS:
        fail(f"{root} lacks a supported ordered-check measurement schema")
    if measurement_schema in NEUTRAL_MEASUREMENT_SCHEMAS:
        validate_neutral_backend_identity(manifest)
    work_budgets = (
        validate_work_budget_manifest(manifest)
        if measurement_schema == MEASUREMENT_SCHEMA_V4
        else None
    )
    driver = manifest.get("driver")
    if not isinstance(driver, dict):
        fail(f"{root} has no driver identity")
    driver_sha256 = require_string(driver.get("sha256"), "driver SHA-256")
    if not re.fullmatch(r"[0-9a-f]{64}", driver_sha256):
        fail(f"invalid driver SHA-256 in {root}")
    driver_path = require_string(driver.get("path"), "driver path")

    try:
        events_bytes = events_path.read_bytes()
    except OSError as error:
        fail(f"cannot read {events_path}: {error}")
    if sha256(events_bytes) != manifest.get("events_sha256"):
        fail(f"events SHA-256 mismatch in {root}")

    checks: list[Check] = []
    seen_check_ids: set[str] = set()
    event_count = 0
    for line_number, raw_line in enumerate(events_bytes.splitlines(), 1):
        if not raw_line.strip():
            fail(f"blank event line {line_number} in {root}")
        try:
            event = json.loads(raw_line)
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            fail(f"invalid event line {line_number} in {root}: {error}")
        if not isinstance(event, dict):
            fail(f"event line {line_number} in {root} is not an object")
        if event.get("event_seq") != event_count:
            fail(f"event sequence gap at line {line_number} in {root}")
        event_count += 1
        if event.get("event") != "check":
            continue

        check_id = require_string(event.get("check_id"), "check ID")
        if check_id in seen_check_ids:
            fail(f"duplicate check ID {check_id} in {root}")
        seen_check_ids.add(check_id)
        query_sha256 = require_string(event.get("query_sha256"), "query SHA-256")
        if not re.fullmatch(r"[0-9a-f]{64}", query_sha256):
            fail(f"invalid query SHA-256 for {check_id} in {root}")
        z3_outcome = require_string(event.get("z3_outcome"), "Z3 outcome")
        axeyum_outcome = require_string(event.get("axeyum_outcome"), "Axeyum outcome")
        if z3_outcome not in OUTCOMES or axeyum_outcome not in OUTCOMES:
            fail(f"invalid backend outcome for {check_id} in {root}")
        if {z3_outcome, axeyum_outcome} & {"error", "no-solver"}:
            fail(f"operational backend result for {check_id} in {root}")
        if z3_outcome in DECIDED and axeyum_outcome in DECIDED:
            if z3_outcome != axeyum_outcome:
                fail(f"decided backend disagreement for {check_id} in {root}")
        execution = require_string(event.get("axeyum_execution"), "Axeyum execution")
        if execution not in EXECUTION_CLASSES:
            fail(f"invalid Axeyum execution class for {check_id} in {root}")
        z3_nanos = require_positive_int(event.get("z3_nanos"), "Z3 timing")
        axeyum_nanos = require_positive_int(event.get("axeyum_nanos"), "Axeyum timing")
        fair_values: dict[str, Any] = {}
        if measurement_schema in FAIR_MEASUREMENT_SCHEMAS:
            fair_cells = (
                FAIR_CELLS_V3
                if measurement_schema in NEUTRAL_MEASUREMENT_SCHEMAS
                else FAIR_CELLS_V2
            )
            for cell in fair_cells:
                cell_outcome = require_string(
                    event.get(f"{cell}_outcome"), f"{cell} outcome"
                )
                if cell_outcome not in OUTCOMES:
                    fail(f"invalid {cell} outcome for {check_id} in {root}")
                if cell_outcome in {"error", "no-solver"}:
                    fail(f"operational {cell} result for {check_id} in {root}")
                fair_values[f"{cell}_outcome"] = cell_outcome
                fair_values[f"{cell}_nanos"] = require_positive_int(
                    event.get(f"{cell}_nanos"), f"{cell} timing"
                )
            decided = {
                fair_values[f"{cell}_outcome"]
                for cell in fair_cells
                if fair_values[f"{cell}_outcome"] in DECIDED
            }
            if len(decided) > 1:
                fail(f"decided fair-cell disagreement for {check_id} in {root}")
            fair_values["z3_warm_execution"] = require_string(
                event.get("z3_warm_execution"), "warm Z3 execution"
            )
            if fair_values["z3_warm_execution"] not in {
                "warm-created",
                "warm-retained",
                "fallback-missing-delta",
                "invalid-direct-delta",
            }:
                fail(f"invalid warm Z3 execution for {check_id} in {root}")
            fair_values["axeyum_warm_execution"] = require_string(
                event.get("axeyum_warm_execution"), "warm Axeyum execution"
            )
            if fair_values["axeyum_warm_execution"] not in EXECUTION_CLASSES:
                fail(f"invalid warm Axeyum execution for {check_id} in {root}")
            if measurement_schema in NEUTRAL_MEASUREMENT_SCHEMAS:
                fair_values["bitwuzla_warm_execution"] = require_string(
                    event.get("bitwuzla_warm_execution"), "warm Bitwuzla execution"
                )
                if (
                    fair_values["bitwuzla_warm_execution"]
                    not in NEUTRAL_WARM_CLASSES
                ):
                    fail(f"invalid warm Bitwuzla execution for {check_id} in {root}")
            aliases = (
                (z3_nanos, fair_values["z3_cold_nanos"], "Z3 timing"),
                (axeyum_nanos, fair_values["axeyum_warm_nanos"], "Axeyum timing"),
                (z3_outcome, fair_values["z3_cold_outcome"], "Z3 outcome"),
                (axeyum_outcome, fair_values["axeyum_warm_outcome"], "Axeyum outcome"),
                (
                    execution,
                    fair_values["axeyum_warm_execution"],
                    "Axeyum execution",
                ),
            )
            for alias, explicit, label in aliases:
                if alias != explicit:
                    fail(f"{label} alias mismatch for {check_id} in {root}")
            if measurement_schema == MEASUREMENT_SCHEMA_V4:
                assert work_budgets is not None
                fair_values["resource_counters"] = validate_resource_counters(
                    event, fair_values, work_budgets, check_id, root
                )
        purpose = require_string(event.get("purpose"), "check purpose")
        active_constraint_count = event.get("active_constraint_count")
        if (
            isinstance(active_constraint_count, bool)
            or not isinstance(active_constraint_count, int)
            or active_constraint_count < 0
        ):
            fail(f"invalid active constraint count for {check_id} in {root}")
        identity = (
            event.get("event_seq"),
            check_id,
            event.get("path_id"),
            query_sha256,
            purpose,
            event.get("scope_digest"),
            active_constraint_count,
            execution,
            fair_values.get("z3_warm_execution"),
            fair_values.get("axeyum_warm_execution"),
            fair_values.get("bitwuzla_warm_execution"),
        )
        checks.append(
            Check(
                identity=identity,
                check_id=check_id,
                query_sha256=query_sha256,
                purpose=purpose,
                active_constraint_count=active_constraint_count,
                z3_outcome=z3_outcome,
                axeyum_outcome=axeyum_outcome,
                z3_nanos=z3_nanos,
                axeyum_nanos=axeyum_nanos,
                axeyum_execution=execution,
                **fair_values,
            )
        )

    if manifest.get("event_count") != event_count:
        fail(f"manifest event count mismatch in {root}")
    if not checks:
        fail(f"trace contains no paired checks: {root}")
    verify_query_artifacts(
        root, manifest, {check.query_sha256 for check in checks}
    )
    return Trace(
        path=root,
        driver_label=pathlib.Path(driver_path).name,
        driver_sha256=driver_sha256,
        configuration_identity=configuration_identity(manifest),
        measurement_schema=measurement_schema,
        checks=tuple(checks),
    )


def geometric_mean(values: Sequence[float]) -> float:
    if not values or any(not math.isfinite(value) or value <= 0 for value in values):
        fail("geometric mean requires finite positive values")
    return math.exp(math.fsum(math.log(value) for value in values) / len(values))


def nearest_rank(values: Sequence[float], quantile: float) -> float:
    if not values or not 0.0 <= quantile <= 1.0:
        fail("invalid nearest-rank input")
    ordered = sorted(values)
    if quantile == 0.0:
        return ordered[0]
    return ordered[min(len(ordered) - 1, math.ceil(quantile * len(ordered)) - 1)]


def bootstrap_geomean_ci(
    values: Sequence[float], samples: int, seed: int
) -> tuple[float, float]:
    if samples <= 0:
        fail("bootstrap sample count must be positive")
    rng = random.Random(seed)
    estimates = [
        geometric_mean([values[rng.randrange(len(values))] for _ in values])
        for _ in range(samples)
    ]
    return nearest_rank(estimates, 0.025), nearest_rank(estimates, 0.975)


def sample_summary(values: Sequence[float]) -> dict[str, Any]:
    if not values:
        fail("cannot summarize an empty sample")
    mean = statistics.fmean(values)
    deviation = statistics.stdev(values) if len(values) > 1 else 0.0
    return {
        "values": list(values),
        "mean": mean,
        "sample_standard_deviation": deviation,
        "coefficient_of_variation": deviation / mean if mean else None,
    }


def latency_summary(values: Sequence[float]) -> dict[str, float]:
    return {
        "p50": nearest_rank(values, 0.50),
        "p90": nearest_rank(values, 0.90),
        "p95": nearest_rank(values, 0.95),
        "p99": nearest_rank(values, 0.99),
    }


def outcome_bucket(check: Check) -> str:
    z3_decided = check.z3_outcome in DECIDED
    axeyum_decided = check.axeyum_outcome in DECIDED
    if z3_decided and axeyum_decided:
        return "both_decided"
    if z3_decided:
        return "z3_only"
    if axeyum_decided:
        return "axeyum_only"
    return "neither"


def population_summary(
    traces: Sequence[Trace],
    indices: Sequence[int],
    bootstrap_samples: int,
    seed: int,
) -> dict[str, Any]:
    if not indices:
        return {"occurrences": 0}
    per_occurrence_ratios: list[float] = []
    z3_occurrence_latency: list[float] = []
    axeyum_occurrence_latency: list[float] = []
    for index in indices:
        z3_values = [trace.checks[index].z3_nanos for trace in traces]
        axeyum_values = [trace.checks[index].axeyum_nanos for trace in traces]
        per_occurrence_ratios.append(
            geometric_mean([z3 / ax for z3, ax in zip(z3_values, axeyum_values)])
        )
        z3_occurrence_latency.append(statistics.median(z3_values))
        axeyum_occurrence_latency.append(statistics.median(axeyum_values))

    geomean = geometric_mean(per_occurrence_ratios)
    ci_low, ci_high = bootstrap_geomean_ci(
        per_occurrence_ratios, bootstrap_samples, seed
    )
    per_run_geomeans = [
        geometric_mean(
            [
                trace.checks[index].z3_nanos / trace.checks[index].axeyum_nanos
                for index in indices
            ]
        )
        for trace in traces
    ]
    return {
        "occurrences": len(indices),
        "speedup_direction": "z3_nanos/axeyum_nanos; greater than 1 favors Axeyum",
        "per_occurrence_geomean_speedup": geomean,
        "bootstrap_95_percent_ci": [ci_low, ci_high],
        "bootstrap_samples": bootstrap_samples,
        "z3_median_per_occurrence_latency_nanos": latency_summary(
            z3_occurrence_latency
        ),
        "axeyum_median_per_occurrence_latency_nanos": latency_summary(
            axeyum_occurrence_latency
        ),
        "per_run_geomean_speedup": sample_summary(per_run_geomeans),
        "_cdf_z3_nanos": z3_occurrence_latency,
        "_cdf_axeyum_nanos": axeyum_occurrence_latency,
    }


def fair_cell_population_summary(
    traces: Sequence[Trace],
    indices: Sequence[int],
    numerator: str,
    denominator: str,
    bootstrap_samples: int,
    seed: int,
) -> dict[str, Any]:
    if not indices:
        return {"occurrences": 0}
    numerator_field = f"{numerator}_nanos"
    denominator_field = f"{denominator}_nanos"
    per_occurrence_ratios: list[float] = []
    numerator_latency: list[float] = []
    denominator_latency: list[float] = []
    for index in indices:
        numerator_values = [
            getattr(trace.checks[index], numerator_field) for trace in traces
        ]
        denominator_values = [
            getattr(trace.checks[index], denominator_field) for trace in traces
        ]
        if any(value is None for value in numerator_values + denominator_values):
            fail("fair-cell timing is absent from a comparison")
        numerator_ints = [int(value) for value in numerator_values]
        denominator_ints = [int(value) for value in denominator_values]
        per_occurrence_ratios.append(
            geometric_mean(
                [
                    left / right
                    for left, right in zip(numerator_ints, denominator_ints)
                ]
            )
        )
        numerator_latency.append(statistics.median(numerator_ints))
        denominator_latency.append(statistics.median(denominator_ints))
    geomean = geometric_mean(per_occurrence_ratios)
    ci_low, ci_high = bootstrap_geomean_ci(
        per_occurrence_ratios, bootstrap_samples, seed
    )
    per_run_geomeans = [
        geometric_mean(
            [
                int(getattr(trace.checks[index], numerator_field))
                / int(getattr(trace.checks[index], denominator_field))
                for index in indices
            ]
        )
        for trace in traces
    ]
    return {
        "occurrences": len(indices),
        "ratio_direction": f"{numerator_field}/{denominator_field}",
        "per_occurrence_geomean_speedup": geomean,
        "bootstrap_95_percent_ci": [ci_low, ci_high],
        "bootstrap_samples": bootstrap_samples,
        "numerator_median_per_occurrence_latency_nanos": latency_summary(
            numerator_latency
        ),
        "denominator_median_per_occurrence_latency_nanos": latency_summary(
            denominator_latency
        ),
        "per_run_geomean_speedup": sample_summary(per_run_geomeans),
    }


def stable_fair_cell_indices(
    traces: Sequence[Trace], numerator: str, denominator: str
) -> list[int]:
    return [
        index
        for index in range(len(traces[0].checks))
        if all(
            getattr(trace.checks[index], f"{numerator}_outcome") in DECIDED
            and getattr(trace.checks[index], f"{denominator}_outcome") in DECIDED
            for trace in traces
        )
    ]


def analyze(
    roots: Sequence[pathlib.Path],
    minimum_repetitions: int = 5,
    bootstrap_samples: int = 10_000,
    seed: int = 0,
) -> dict[str, Any]:
    if minimum_repetitions < 2:
        fail("minimum repetitions must be at least 2")
    if len(roots) < minimum_repetitions:
        fail(
            f"need at least {minimum_repetitions} repetitions, received {len(roots)}"
        )
    traces = [load_trace(root) for root in roots]
    baseline = traces[0]
    baseline_identities = tuple(check.identity for check in baseline.checks)
    for trace in traces[1:]:
        if trace.driver_sha256 != baseline.driver_sha256:
            fail(f"driver identity drift in {trace.path}")
        if trace.configuration_identity != baseline.configuration_identity:
            fail(f"configuration/environment drift in {trace.path}")
        identities = tuple(check.identity for check in trace.checks)
        if identities != baseline_identities:
            fail(f"fixed-work check identity drift in {trace.path}")

    outcome_fields = ["z3_outcome", "axeyum_outcome"]
    if baseline.measurement_schema in FAIR_MEASUREMENT_SCHEMAS:
        fair_cells = (
            FAIR_CELLS_V3
            if baseline.measurement_schema in NEUTRAL_MEASUREMENT_SCHEMAS
            else FAIR_CELLS_V2
        )
        outcome_fields.extend(f"{cell}_outcome" for cell in fair_cells)
    for index, baseline_check in enumerate(baseline.checks):
        for field in outcome_fields:
            all_outcomes = {
                getattr(trace.checks[index], field) for trace in traces
            }
            if baseline.measurement_schema == MEASUREMENT_SCHEMA_V4 and len(all_outcomes) > 1:
                fail(
                    f"deterministic work-bound outcome drift for {baseline_check.check_id} "
                    f"field {field} across repetitions"
                )
            decided_outcomes = {
                outcome for outcome in all_outcomes if outcome in DECIDED
            }
            if len(decided_outcomes) > 1:
                fail(
                    f"decided outcome drift for {baseline_check.check_id} "
                    f"field {field} across repetitions"
                )

    per_run_buckets: list[dict[str, int]] = []
    for trace in traces:
        buckets = {
            "both_decided": 0,
            "z3_only": 0,
            "axeyum_only": 0,
            "neither": 0,
        }
        for check in trace.checks:
            bucket = outcome_bucket(check)
            buckets[bucket] += 1
        per_run_buckets.append(buckets)

    stable_both_decided = [
        index
        for index in range(len(baseline.checks))
        if all(outcome_bucket(trace.checks[index]) == "both_decided" for trace in traces)
    ]
    excluded = len(baseline.checks) - len(stable_both_decided)
    if not stable_both_decided:
        fail("no occurrence was decided by both backends in every repetition")

    class_counts: dict[str, int] = {}
    for check in baseline.checks:
        class_counts[check.axeyum_execution] = class_counts.get(check.axeyum_execution, 0) + 1
    class_populations: dict[str, Any] = {}
    for offset, execution in enumerate(sorted(class_counts)):
        indices = [
            index
            for index in stable_both_decided
            if baseline.checks[index].axeyum_execution == execution
        ]
        class_populations[execution] = population_summary(
            traces, indices, bootstrap_samples, seed + offset + 1
        )

    primary = population_summary(
        traces, stable_both_decided, bootstrap_samples, seed
    )
    four_cell_comparisons: dict[str, Any] | None = None
    four_cell_cdf: dict[str, list[float]] | None = None
    if baseline.measurement_schema == MEASUREMENT_SCHEMA_V2:
        comparison_specs = (
            ("cold_z3_over_axeyum", "z3_cold", "axeyum_cold"),
            ("warm_z3_over_axeyum", "z3_warm", "axeyum_warm"),
            ("z3_cold_over_warm", "z3_cold", "z3_warm"),
            ("axeyum_cold_over_warm", "axeyum_cold", "axeyum_warm"),
        )
        four_cell_comparisons = {}
        for offset, (name, numerator, denominator) in enumerate(comparison_specs):
            indices = stable_fair_cell_indices(traces, numerator, denominator)
            four_cell_comparisons[name] = fair_cell_population_summary(
                traces,
                indices,
                numerator,
                denominator,
                bootstrap_samples,
                seed + 100 + offset,
            )
        all_four_indices = [
            index
            for index in range(len(baseline.checks))
            if all(
                all(
                    getattr(trace.checks[index], f"{cell}_outcome") in DECIDED
                    for cell in FAIR_CELLS_V2
                )
                for trace in traces
            )
        ]
        four_cell_cdf = {
            cell: [
                statistics.median(
                    [int(getattr(trace.checks[index], f"{cell}_nanos")) for trace in traces]
                )
                for index in all_four_indices
            ]
            for cell in FAIR_CELLS_V2
        }
    six_cell_comparisons: dict[str, Any] | None = None
    six_cell_cdf: dict[str, list[float]] | None = None
    stable_all_six: list[int] = []
    six_cell_outcome_counts: list[dict[str, int]] | None = None
    warm_execution_counts: list[dict[str, dict[str, int]]] | None = None
    neutral_gate: dict[str, Any] | None = None
    work_bound_stop_reason_counts: list[dict[str, dict[str, int]]] | None = None
    deterministic_work_gate: dict[str, Any] | None = None
    if baseline.measurement_schema in NEUTRAL_MEASUREMENT_SCHEMAS:
        comparison_specs = (
            ("cold_z3_over_axeyum", "z3_cold", "axeyum_cold"),
            ("cold_z3_over_bitwuzla", "z3_cold", "bitwuzla_cold"),
            ("cold_axeyum_over_bitwuzla", "axeyum_cold", "bitwuzla_cold"),
            ("warm_z3_over_axeyum", "z3_warm", "axeyum_warm"),
            ("warm_z3_over_bitwuzla", "z3_warm", "bitwuzla_warm"),
            ("warm_axeyum_over_bitwuzla", "axeyum_warm", "bitwuzla_warm"),
            ("z3_cold_over_warm", "z3_cold", "z3_warm"),
            ("axeyum_cold_over_warm", "axeyum_cold", "axeyum_warm"),
            ("bitwuzla_cold_over_warm", "bitwuzla_cold", "bitwuzla_warm"),
        )
        six_cell_comparisons = {}
        for offset, (name, numerator, denominator) in enumerate(comparison_specs):
            indices = stable_fair_cell_indices(traces, numerator, denominator)
            six_cell_comparisons[name] = fair_cell_population_summary(
                traces,
                indices,
                numerator,
                denominator,
                bootstrap_samples,
                seed + 200 + offset,
            )
        stable_all_six = [
            index
            for index in range(len(baseline.checks))
            if all(
                all(
                    getattr(trace.checks[index], f"{cell}_outcome") in DECIDED
                    for cell in FAIR_CELLS_V3
                )
                for trace in traces
            )
        ]
        six_cell_outcome_counts = []
        for trace in traces:
            all_decided = sum(
                all(getattr(check, f"{cell}_outcome") in DECIDED for cell in FAIR_CELLS_V3)
                for check in trace.checks
            )
            six_cell_outcome_counts.append(
                {
                    "all_six_decided": all_decided,
                    "any_nondecision": len(trace.checks) - all_decided,
                }
            )
        warm_fields = {
            "z3": "z3_warm_execution",
            "axeyum": "axeyum_warm_execution",
            "bitwuzla": "bitwuzla_warm_execution",
        }
        warm_execution_counts = []
        for trace in traces:
            per_solver: dict[str, dict[str, int]] = {}
            for solver, field in warm_fields.items():
                counts: dict[str, int] = {}
                for check in trace.checks:
                    execution = getattr(check, field)
                    if execution is None:
                        fail(f"missing v3 warm execution class for {solver}")
                    counts[execution] = counts.get(execution, 0) + 1
                per_solver[solver] = counts
            warm_execution_counts.append(per_solver)
        six_cell_cdf = {
            cell: [
                statistics.median(
                    [int(getattr(trace.checks[index], f"{cell}_nanos")) for trace in traces]
                )
                for index in stable_all_six
            ]
            for cell in FAIR_CELLS_V3
        }
        gate_reasons: list[str] = []
        if len(stable_all_six) != len(baseline.checks):
            gate_reasons.append("not_all_occurrences_six_way_decided")
        for solver, field in warm_fields.items():
            if any(
                getattr(check, field) not in DIRECT_WARM_CLASSES
                for trace in traces
                for check in trace.checks
            ):
                gate_reasons.append(f"non_pure_warm_execution:{solver}")
        for name in (
            "warm_z3_over_axeyum",
            "warm_z3_over_bitwuzla",
            "warm_axeyum_over_bitwuzla",
        ):
            comparison = six_cell_comparisons[name]
            per_run = comparison.get("per_run_geomean_speedup")
            if per_run is None:
                gate_reasons.append(f"no_stable_pair_population:{name}")
            elif per_run["coefficient_of_variation"] > 0.03:
                gate_reasons.append(f"warm_process_cv_above_0.03:{name}")
        neutral_gate = {"accepted": not gate_reasons, "reasons": gate_reasons}
        if baseline.measurement_schema == MEASUREMENT_SCHEMA_V4:
            work_bound_stop_reason_counts = []
            deterministic_gate_reasons: list[str] = []
            for trace in traces:
                per_cell: dict[str, dict[str, int]] = {}
                for cell in FAIR_CELLS_V3:
                    counts = {
                        "decided": 0,
                        "resource-limit": 0,
                        "wall-timeout": 0,
                        "other": 0,
                    }
                    for check in trace.checks:
                        assert check.resource_counters is not None
                        reason = check.resource_counters[cell]["stop_reason"]
                        counts["decided" if reason is None else reason] += 1
                    per_cell[cell] = counts
                    if counts["wall-timeout"]:
                        deterministic_gate_reasons.append(f"wall-timeout:{cell}")
                    if counts["other"]:
                        deterministic_gate_reasons.append(f"other-unknown:{cell}")
                work_bound_stop_reason_counts.append(per_cell)
            for index, baseline_check in enumerate(baseline.checks):
                for cell in FAIR_CELLS_V3:
                    reasons = {
                        trace.checks[index].resource_counters[cell]["stop_reason"]
                        for trace in traces
                        if trace.checks[index].resource_counters is not None
                    }
                    if len(reasons) > 1:
                        fail(
                            f"deterministic work-bound stop-reason drift for "
                            f"{baseline_check.check_id} cell {cell}"
                        )
            deterministic_work_gate = {
                "accepted": not deterministic_gate_reasons,
                "reasons": sorted(set(deterministic_gate_reasons)),
            }
    warm_count = sum(class_counts.get(name, 0) for name in PURE_WARM_CLASSES)
    retained_warm_count = class_counts.get("warm-retained", 0)
    report = {
        "schema": "axeyum-glaurung-paired-analysis-v1",
        "input_measurement_schema": baseline.measurement_schema,
        "driver": {
            "label": baseline.driver_label,
            "sha256": baseline.driver_sha256,
        },
        "configuration_identity": json.loads(baseline.configuration_identity),
        "repetitions": len(traces),
        "trace_paths": [str(trace.path) for trace in traces],
        "fixed_work_checks_per_repetition": len(baseline.checks),
        "outcome_buckets_per_repetition": per_run_buckets,
        "stable_both_decided_occurrences": len(stable_both_decided),
        "excluded_from_primary_for_any_nondecision": excluded,
        "axeyum_execution_counts_per_repetition": class_counts,
        "pure_warm_execution_rate": warm_count / len(baseline.checks),
        "retained_warm_execution_rate": retained_warm_count / len(baseline.checks),
        "primary_both_decided": primary,
        "by_axeyum_execution": class_populations,
        "methodology": {
            "pairing_unit": "stable ordered check occurrence",
            "primary_population": (
                "occurrences decided by both backends in every repetition"
            ),
            "latency_distribution_unit": (
                "per-occurrence median across fixed-work repetitions"
            ),
            "quantiles": "nearest-rank",
            "bootstrap_seed": seed,
            "ratio_of_sums_reported": False,
            "operational_errors_allowed": False,
        },
    }
    if four_cell_comparisons is not None:
        report["four_cell_comparisons"] = four_cell_comparisons
        report["_four_cell_cdf"] = four_cell_cdf
    if six_cell_comparisons is not None:
        report["six_cell_comparisons"] = six_cell_comparisons
        report["stable_all_six_decided_occurrences"] = len(stable_all_six)
        report["six_cell_outcome_counts_per_repetition"] = six_cell_outcome_counts
        report["warm_execution_counts_per_repetition"] = warm_execution_counts
        report["neutral_regime_gate"] = neutral_gate
        report["_six_cell_cdf"] = six_cell_cdf
    if work_bound_stop_reason_counts is not None:
        report["work_bound_stop_reason_counts_per_repetition"] = (
            work_bound_stop_reason_counts
        )
        report["deterministic_work_gate"] = deterministic_work_gate
    return report


def write_cdf(report: dict[str, Any], output_dir: pathlib.Path) -> None:
    try:
        import matplotlib.pyplot as plt  # type: ignore[import-not-found]
    except ImportError as error:
        fail(f"--cdf-dir requires matplotlib: {error}")
    primary = report["primary_both_decided"]
    z3_values = primary.pop("_cdf_z3_nanos")
    axeyum_values = primary.pop("_cdf_axeyum_nanos")
    for population in report["by_axeyum_execution"].values():
        population.pop("_cdf_z3_nanos", None)
        population.pop("_cdf_axeyum_nanos", None)
    output_dir.mkdir(parents=True, exist_ok=True)
    stem = re.sub(r"[^A-Za-z0-9_.-]+", "-", report["driver"]["label"])
    csv_path = output_dir / f"{stem}-latency-cdf.csv"
    with csv_path.open("w", encoding="utf-8", newline="") as output:
        writer = csv.writer(output, lineterminator="\n")
        writer.writerow(["backend", "latency_nanos", "cumulative_fraction"])
        for backend, values in [("z3", z3_values), ("axeyum", axeyum_values)]:
            ordered = sorted(values)
            for rank, value in enumerate(ordered, 1):
                writer.writerow([backend, value, rank / len(ordered)])

    for backend, values in [("Z3", z3_values), ("Axeyum", axeyum_values)]:
        ordered = sorted(value / 1_000.0 for value in values)
        cumulative = [rank / len(ordered) for rank in range(1, len(ordered) + 1)]
        plt.step(ordered, cumulative, where="post", label=backend)
    plt.xscale("log")
    plt.xlabel("latency (microseconds, log scale)")
    plt.ylabel("cumulative fraction")
    plt.title(f"Paired both-decided latency: {report['driver']['label']}")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / f"{stem}-latency-cdf.png", dpi=180)
    plt.close()

    for private_key, suffix, title in (
        ("_four_cell_cdf", "four-cell", "Four-cell"),
        ("_six_cell_cdf", "six-cell", "Six-cell"),
    ):
        cell_values = report.pop(private_key, None)
        if cell_values is None:
            continue
        cell_csv_path = output_dir / f"{stem}-{suffix}-latency-cdf.csv"
        with cell_csv_path.open("w", encoding="utf-8", newline="") as output:
            writer = csv.writer(output, lineterminator="\n")
            writer.writerow(["cell", "latency_nanos", "cumulative_fraction"])
            for cell, values in cell_values.items():
                ordered = sorted(values)
                for rank, value in enumerate(ordered, 1):
                    writer.writerow([cell, value, rank / len(ordered)])
        for cell, values in cell_values.items():
            ordered = sorted(value / 1_000.0 for value in values)
            cumulative = [rank / len(ordered) for rank in range(1, len(ordered) + 1)]
            plt.step(ordered, cumulative, where="post", label=cell)
        plt.xscale("log")
        plt.xlabel("latency (microseconds, log scale)")
        plt.ylabel("cumulative fraction")
        plt.title(f"{title} paired latency: {report['driver']['label']}")
        plt.grid(True, which="both", alpha=0.25)
        plt.legend()
        plt.tight_layout()
        plt.savefig(output_dir / f"{stem}-{suffix}-latency-cdf.png", dpi=180)
        plt.close()


def strip_private_cdf_values(report: dict[str, Any]) -> None:
    report["primary_both_decided"].pop("_cdf_z3_nanos", None)
    report["primary_both_decided"].pop("_cdf_axeyum_nanos", None)
    for population in report["by_axeyum_execution"].values():
        population.pop("_cdf_z3_nanos", None)
        population.pop("_cdf_axeyum_nanos", None)
    report.pop("_four_cell_cdf", None)
    report.pop("_six_cell_cdf", None)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("traces", nargs="+", type=pathlib.Path)
    parser.add_argument("--output", type=pathlib.Path)
    parser.add_argument("--cdf-dir", type=pathlib.Path)
    parser.add_argument("--minimum-repetitions", type=int, default=5)
    parser.add_argument("--bootstrap-samples", type=int, default=10_000)
    parser.add_argument("--seed", type=int, default=0)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        report = analyze(
            args.traces,
            minimum_repetitions=args.minimum_repetitions,
            bootstrap_samples=args.bootstrap_samples,
            seed=args.seed,
        )
        if args.cdf_dir is not None:
            write_cdf(report, args.cdf_dir)
        else:
            strip_private_cdf_values(report)
        rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.output is None:
            sys.stdout.write(rendered)
        else:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(rendered, encoding="utf-8")
    except AnalysisError as error:
        print(f"paired trace analysis failed: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
