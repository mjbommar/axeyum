#!/usr/bin/env python3
"""Fail-closed analysis for repeated real-query QF_BV faithfulness artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from collections import Counter
from pathlib import Path
from typing import Any, NoReturn, Sequence


SUPPORTED_ARTIFACT_VERSIONS = (33, 34)
SCHEMA = "axeyum-qfbv-real-faithfulness-analysis-v1"
MIN_REPETITIONS = 2


class AnalysisError(ValueError):
    """An artifact violates the real-query faithfulness contract."""


def fail(message: str) -> NoReturn:
    raise AnalysisError(message)


def mapping(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{label} must be an object")
    return value


def sequence(value: Any, label: str) -> list[Any]:
    if not isinstance(value, list):
        fail(f"{label} must be an array")
    return value


def integer(value: Any, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        fail(f"{label} must be an integer")
    return value


def boolean(value: Any, label: str) -> bool:
    if not isinstance(value, bool):
        fail(f"{label} must be a boolean")
    return value


def number(value: Any, label: str) -> float:
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        fail(f"{label} must be a number")
    result = float(value)
    if not math.isfinite(result):
        fail(f"{label} must be finite")
    return result


def string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        fail(f"{label} must be a nonempty string")
    return value


def load(path: Path) -> tuple[dict[str, Any], str]:
    raw = path.read_bytes()
    try:
        value = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"{path}: invalid JSON: {error}")
    return mapping(value, str(path)), hashlib.sha256(raw).hexdigest()


def require_zero(record: dict[str, Any], keys: Sequence[str], label: str) -> None:
    for key in keys:
        if integer(record.get(key), f"{label}.{key}") != 0:
            fail(f"{label}.{key} must be zero")


def validate_config(
    config: dict[str, Any], path: Path, artifact_version: int
) -> dict[str, Any]:
    expected = {
        "backend_kind": "sat-bv",
        "logic": "QF_BV",
        "jobs": 1,
        "manifest_validation_jobs": 1,
        "prove_unsat": True,
        "certify_end_to_end_unsat": True,
        "compare_z3": True,
        "require_in_process_z3": True,
        "require_reproducible_run": True,
        "require_deterministic_resources": True,
        "preprocess": False,
        "demand_bit_slicing": False,
        "range_demand_slicing": False,
        "cnf_inprocessing": False,
        "cnf_vivify": False,
        "native_cdcl": False,
    }
    for key, value in expected.items():
        if config.get(key) != value:
            fail(f"{path}: config.{key} must be {value!r}")
    rewrite = mapping(config.get("rewrite"), f"{path}: config.rewrite")
    query_plan = mapping(config.get("query_plan"), f"{path}: config.query_plan")
    if rewrite.get("mode") != "off" or query_plan.get("mode") != "full":
        fail(f"{path}: certification requires raw rewrite-off/full-query policy")
    deadline = integer(
        config.get("end_to_end_deadline_ms"),
        f"{path}: config.end_to_end_deadline_ms",
    )
    if not 1 <= deadline <= 600_000:
        fail(f"{path}: end-to-end deadline is out of range")
    source = mapping(
        mapping(config.get("experiment"), f"{path}: config.experiment").get("source"),
        f"{path}: config.experiment.source",
    )
    if source.get("dirty") is not False:
        fail(f"{path}: source must be clean")
    manifest = mapping(config.get("corpus_manifest"), f"{path}: corpus_manifest")
    selected = integer(manifest.get("selected_entries"), f"{path}: selected_entries")
    if selected <= 0:
        fail(f"{path}: manifest must select a nonempty exact population")
    identity = {
        "config_hash": string(config.get("config_hash"), f"{path}: config_hash"),
        "environment_hash": string(
            mapping(config.get("experiment"), f"{path}: experiment").get(
                "environment_hash"
            ),
            f"{path}: environment_hash",
        ),
        "source_revision": string(source.get("revision"), f"{path}: source_revision"),
        "manifest_hash": string(manifest.get("content_hash"), f"{path}: manifest_hash"),
        "manifest_name": string(manifest.get("name"), f"{path}: manifest_name"),
        "selected_entries": selected,
        "selected_tier": string(
            manifest.get("selected_tier"), f"{path}: selected_tier"
        ),
        "deadline_ms": deadline,
    }
    if artifact_version >= 34:
        process_timeout = integer(
            config.get("end_to_end_process_timeout_ms"),
            f"{path}: config.end_to_end_process_timeout_ms",
        )
        if not 1 <= process_timeout <= 600_000:
            fail(f"{path}: whole-certificate process timeout is out of range")
        identity["process_timeout_ms"] = process_timeout
        identity["isolation"] = "subprocess-hard-timeout"
    return identity


def validate_artifact(
    artifact: dict[str, Any], path: Path
) -> tuple[int, dict[str, Any], dict[str, tuple[str, ...]], dict[str, Any]]:
    artifact_version = integer(artifact.get("version"), f"{path}: version")
    if artifact_version not in SUPPORTED_ARTIFACT_VERSIONS:
        fail(f"{path}: expected artifact version in {SUPPORTED_ARTIFACT_VERSIONS}")
    config = mapping(artifact.get("config"), f"{path}: config")
    identity = validate_config(config, path, artifact_version)
    summary = mapping(artifact.get("summary"), f"{path}: summary")
    files = integer(summary.get("files"), f"{path}: summary.files")
    sat = integer(summary.get("sat"), f"{path}: summary.sat")
    unsat = integer(summary.get("unsat"), f"{path}: summary.unsat")
    if files != identity["selected_entries"] or files != sat + unsat:
        fail(f"{path}: complete decided population accounting failed")
    if unsat <= 0:
        fail(f"{path}: UNSAT assurance denominator must be nonempty")
    require_zero(
        summary,
        ("unknown", "unsupported", "errors", "disagree", "model_replay_failures"),
        f"{path}: summary",
    )
    manifest = mapping(summary.get("manifest"), f"{path}: summary.manifest")
    oracle = mapping(summary.get("oracle"), f"{path}: summary.oracle")
    if any(integer(manifest.get(key), f"{path}: manifest.{key}") != files for key in ("expected", "compared", "agree")):
        fail(f"{path}: manifest did not agree on every row")
    if integer(manifest.get("disagree"), f"{path}: manifest.disagree") != 0:
        fail(f"{path}: manifest disagreement")
    if any(integer(oracle.get(key), f"{path}: oracle.{key}") != files for key in ("compared", "agree")):
        fail(f"{path}: oracle did not agree on every row")
    require_zero(oracle, ("disagree", "skipped"), f"{path}: oracle")

    proof = mapping(summary.get("unsat_proof_replay"), f"{path}: proof")
    if proof.get("requested") is not True or integer(proof.get("checked"), f"{path}: proof.checked") != unsat:
        fail(f"{path}: every UNSAT must carry checked CNF DRAT")
    if integer(proof.get("missing"), f"{path}: proof.missing") != 0:
        fail(f"{path}: missing CNF DRAT")
    end = mapping(summary.get("end_to_end_unsat"), f"{path}: end_to_end")
    if end.get("requested") is not True or end.get("deadline_ms") != identity["deadline_ms"]:
        fail(f"{path}: end-to-end policy mismatch")
    if integer(end.get("attempted"), f"{path}: attempted") != unsat:
        fail(f"{path}: every UNSAT must remain in the end-to-end denominator")
    certified = integer(end.get("certified"), f"{path}: certified")
    not_certified = integer(end.get("not_certified"), f"{path}: not_certified")
    require_zero(
        end,
        ("satisfiable_contradictions", "recheck_failures", "errors"),
        f"{path}: end_to_end",
    )
    if certified + not_certified != unsat or end.get("attempted_partitioned") is not True:
        fail(f"{path}: end-to-end outcome partition is incomplete")
    hard_timeouts = 0
    if artifact_version >= 34:
        if end.get("process_timeout_ms") != identity["process_timeout_ms"]:
            fail(f"{path}: whole-certificate process timeout mismatch")
        if end.get("isolation") != "subprocess-hard-timeout":
            fail(f"{path}: artifact-v34 faithfulness requires subprocess isolation")
        hard_timeouts = integer(end.get("hard_timeouts"), f"{path}: hard_timeouts")
        if not 0 <= hard_timeouts <= not_certified:
            fail(f"{path}: hard timeouts must be a subset of not-certified rows")
        hard_timeout_paths = sequence(
            end.get("hard_timeout_paths"), f"{path}: hard_timeout_paths"
        )
        if len(hard_timeout_paths) != hard_timeouts:
            fail(f"{path}: hard-timeout path count mismatch")
    elapsed = mapping(end.get("elapsed"), f"{path}: end_to_end.elapsed")
    elapsed_values = {
        key: number(elapsed.get(key), f"{path}: end_to_end.elapsed.{key}")
        for key in ("min_ms", "p50_ms", "mean_ms", "p95_ms", "max_ms")
    }
    if not (
        0.0
        <= elapsed_values["min_ms"]
        <= elapsed_values["p50_ms"]
        <= elapsed_values["p95_ms"]
        <= elapsed_values["max_ms"]
    ):
        fail(f"{path}: end-to-end elapsed percentiles are not ordered")
    if not (
        elapsed_values["min_ms"]
        <= elapsed_values["mean_ms"]
        <= elapsed_values["max_ms"]
    ):
        fail(f"{path}: end-to-end elapsed mean is outside the observed range")

    rows = sequence(artifact.get("instances"), f"{path}: instances")
    if len(rows) != files:
        fail(f"{path}: instance cardinality mismatch")
    identities: dict[str, tuple[str, ...]] = {}
    family_counts: Counter[str] = Counter()
    status_counts: Counter[str] = Counter()
    for index, raw in enumerate(rows):
        row = mapping(raw, f"{path}: instances[{index}]")
        outcome = string(row.get("outcome"), f"{path}: outcome")
        if outcome not in ("sat", "unsat"):
            fail(f"{path}: undecided instance in complete population")
        member = mapping(row.get("corpus_manifest"), f"{path}: row manifest")
        member_path = string(member.get("path"), f"{path}: member path")
        expected = string(member.get("expected"), f"{path}: expected")
        content_hash = string(member.get("content_hash"), f"{path}: content_hash")
        family = string(member.get("family"), f"{path}: family")
        if expected != outcome or boolean(member.get("decision_agrees"), f"{path}: manifest agreement") is not True:
            fail(f"{path}: row disagrees with manifest: {member_path}")
        row_oracle = mapping(row.get("oracle"), f"{path}: row oracle")
        if row_oracle.get("outcome") != outcome or row_oracle.get("decision_agrees") is not True:
            fail(f"{path}: row disagrees with oracle: {member_path}")
        proof_status = string(row.get("unsat_proof_replay"), f"{path}: proof status")
        row_end = mapping(row.get("end_to_end_unsat"), f"{path}: row end-to-end")
        end_status = string(
            row_end.get("status"),
            f"{path}: end-to-end status",
        )
        hard_timeout = False
        if artifact_version >= 34:
            if row_end.get("isolation") != "subprocess-hard-timeout":
                fail(f"{path}: row lacks subprocess isolation: {member_path}")
            if row_end.get("process_timeout_ms") != identity["process_timeout_ms"]:
                fail(f"{path}: row process-timeout policy mismatch: {member_path}")
            hard_timeout = boolean(
                row_end.get("hard_timeout"), f"{path}: row hard_timeout"
            )
            if hard_timeout and end_status != "not-certified":
                fail(f"{path}: only not-certified rows may hard-timeout: {member_path}")
        if outcome == "unsat":
            if proof_status != "checked" or end_status not in ("certified", "not-certified"):
                fail(f"{path}: invalid UNSAT assurance status: {member_path}")
            family_counts[family] += 1
        elif proof_status != "not-applicable" or end_status != "not-applicable":
            fail(f"{path}: SAT row received UNSAT assurance credit: {member_path}")
        if member_path in identities:
            fail(f"{path}: duplicate manifest member {member_path}")
        identities[member_path] = (
            content_hash,
            outcome,
            end_status,
            *(('hard-timeout',) if hard_timeout else ()),
        )
        status_counts[end_status] += 1
    if status_counts["certified"] != certified or status_counts["not-certified"] != not_certified:
        fail(f"{path}: per-row and summary end-to-end counts differ")
    if artifact_version >= 34:
        row_hard_timeouts = sum(
            1 for value in identities.values() if value[-1] == "hard-timeout"
        )
        if row_hard_timeouts != hard_timeouts:
            fail(f"{path}: per-row and summary hard-timeout counts differ")
    return artifact_version, identity, identities, {
        "files": files,
        "sat": sat,
        "unsat": unsat,
        "certified": certified,
        "not_certified": not_certified,
        "hard_timeouts": hard_timeouts,
        "family_counts": dict(sorted(family_counts.items())),
        "elapsed": elapsed,
    }


def analyze(paths: Sequence[Path]) -> dict[str, Any]:
    if len(paths) < MIN_REPETITIONS:
        fail(f"need at least {MIN_REPETITIONS} independent artifacts")
    reference_identity = None
    reference_rows = None
    reference_version = None
    records = []
    summaries = []
    for path in paths:
        artifact, digest = load(path)
        artifact_version, identity, rows, summary = validate_artifact(artifact, path)
        if reference_identity is None:
            reference_version = artifact_version
            reference_identity = identity
            reference_rows = rows
        elif artifact_version != reference_version:
            fail(f"{path}: artifact version drift")
        elif identity != reference_identity:
            fail(f"{path}: configuration, environment, source, or manifest identity drift")
        elif rows != reference_rows:
            fail(f"{path}: per-query outcome or certification drift")
        records.append({"path": path.name, "sha256": digest})
        summaries.append(summary)
    assert (
        reference_version is not None
        and reference_identity is not None
        and reference_rows is not None
    )
    result = {
        "schema": SCHEMA,
        "source_artifact_version": reference_version,
        "contract": {
            "repetitions": len(paths),
            "population": "every member of one exact content-hashed manifest",
            "unsat_denominator": "every primary UNSAT; not-certified rows are retained",
            "fatal": "manifest/oracle disagreement, CNF proof missing, satisfiable contradiction, certificate recheck failure, operational error, or identity drift",
            "timing": (
                "descriptive assurance work only; hard subprocess timeout covers parse, construction, proof searches, and completed-proof checking"
                if reference_version >= 34
                else "descriptive assurance work only; cooperative deadline excludes construction and completed-proof checking"
            ),
        },
        "identity": reference_identity,
        "population": {
            "files": summaries[0]["files"],
            "sat": summaries[0]["sat"],
            "unsat": summaries[0]["unsat"],
            "unsat_family_counts": summaries[0]["family_counts"],
        },
        "coverage": {
            "attempted_per_run": summaries[0]["unsat"],
            "certified_per_run": [value["certified"] for value in summaries],
            "not_certified_per_run": [value["not_certified"] for value in summaries],
            "stable_per_query": True,
            "coverage_percent": 100.0 * summaries[0]["certified"] / summaries[0]["unsat"],
        },
        "assurance_elapsed_distributions": [value["elapsed"] for value in summaries],
        "artifacts": records,
    }
    if reference_version >= 34:
        result["coverage"]["hard_timeouts_per_run"] = [
            value["hard_timeouts"] for value in summaries
        ]
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifacts", nargs="+", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    result = analyze(args.artifacts)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    try:
        main()
    except AnalysisError as error:
        raise SystemExit(f"faithfulness analysis failed: {error}") from error
