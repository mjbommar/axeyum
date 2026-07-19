#!/usr/bin/env python3
"""Validate ADR-0277's fixed 12-process unprofiled timing protocol."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import statistics
from pathlib import Path
from typing import Any


SCHEMA = "axeyum.direct-root-parity-memo-timing.v1"
SCHEDULE = ("B", "C", "C", "B", "B", "C", "C", "B", "B", "C", "C", "B")
BASELINE_SOURCE = "6ff05905131b58a8cfa1c15e91ea97c9304f5ead"
CANDIDATE_SOURCE = "900f69973c90c0655dfcfd564fc9b67c44388506"
BASELINE_BINARY_SHA256 = "c33065e4bf353ec1ccbb37c30152cb8b046eec2e4232f4062a4e1925217bffc4"
CANDIDATE_BINARY_SHA256 = "dcc25e2442623dae583a16b92a4824d881d633aaf40e19add192f09414275c6e"
MANIFEST_SHA256 = "sha256:7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064"
FAMILIES = ("arithmetic", "comparison", "mixed", "register-slice", "slice-partial", "trivial")
STRUCTURAL_STATS = ("aig_nodes", "cnf_variables", "cnf_clauses", "cnf_clauses_emitted")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def load_json(path: Path) -> tuple[dict[str, Any], str]:
    data = path.read_bytes()
    value = json.loads(data)
    require(isinstance(value, dict), f"expected JSON object: {path}")
    return value, hashlib.sha256(data).hexdigest()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def geometric_mean(values: list[float]) -> float:
    require(values and all(value > 0.0 and math.isfinite(value) for value in values), "invalid ratio")
    return math.exp(statistics.fmean(math.log(value) for value in values))


def coefficient_of_variation(values: list[float]) -> float:
    mean = statistics.fmean(values)
    require(mean > 0.0, "nonpositive timing mean")
    return statistics.stdev(values) / mean * 100.0


def exhaustive_bootstrap_upper(values: list[float], percentile: float = 0.95) -> float:
    require(len(values) == 6, "bootstrap requires six paired ratios")
    samples = sorted(
        geometric_mean([values[index] for index in indices])
        for indices in itertools.product(range(len(values)), repeat=len(values))
    )
    rank = max(0, math.ceil(percentile * len(samples)) - 1)
    return samples[rank]


def source_revision(artifact: dict[str, Any]) -> str | None:
    return artifact.get("config", {}).get("experiment", {}).get("source", {}).get("revision")


def validate_artifact(artifact: dict[str, Any], cell: str, label: str) -> None:
    require(artifact.get("version") == 37, f"{label} artifact version drift")
    config = artifact.get("config", {})
    summary = artifact.get("summary", {})
    instances = artifact.get("instances")
    require(config.get("profile_cnf_construction") is False, f"{label} is profiled")
    require(config.get("backend_kind") == "sat-bv", f"{label} backend drift")
    require(config.get("jobs") == 1, f"{label} worker drift")
    require(config.get("require_reproducible_run") is True, f"{label} reproducibility gate absent")
    require(config.get("require_deterministic_resources") is True, f"{label} resource gate absent")
    require(config.get("require_in_process_z3") is True, f"{label} Z3 gate absent")
    require(config.get("corpus_manifest", {}).get("content_hash") == MANIFEST_SHA256, f"{label} manifest drift")
    expected_source = BASELINE_SOURCE if cell == "B" else CANDIDATE_SOURCE
    require(source_revision(artifact) == expected_source, f"{label} source drift")
    require(isinstance(instances, list) and len(instances) == 162, f"{label} instance count drift")
    require(summary.get("files") == 162, f"{label} file count drift")
    require(summary.get("sat") == 88 and summary.get("unsat") == 74, f"{label} verdict count drift")
    for key in ("unknown", "unsupported", "errors", "disagree", "model_replay_failures"):
        require(summary.get(key) == 0, f"{label} summary.{key} is nonzero")
    require(summary.get("manifest", {}).get("agree") == 162, f"{label} manifest disagreement")
    require(summary.get("oracle", {}).get("agree") == 162, f"{label} oracle disagreement")
    require(summary.get("oracle", {}).get("skipped") == 0, f"{label} oracle skip")
    require(summary.get("layer_attribution", {}).get("model_replay_instances") == 88, f"{label} replay population drift")


def run_totals(artifact: dict[str, Any]) -> tuple[float, dict[str, float]]:
    total = 0.0
    families = {family: 0.0 for family in FAMILIES}
    for instance in artifact["instances"]:
        value = float(instance["cold_total_ms"])
        require(value > 0.0 and math.isfinite(value), "invalid cold_total_ms")
        family = instance["corpus_manifest"]["family"]
        require(family in families, "unknown family")
        total += value
        families[family] += value
    return total, families


def validate_cross_run_structure(artifacts: list[dict[str, Any]]) -> None:
    reference = artifacts[0]["instances"]
    for run_index, artifact in enumerate(artifacts[1:], start=2):
        for instance_index, (before, after) in enumerate(
            zip(reference, artifact["instances"], strict=True)
        ):
            label = f"run {run_index} instance {instance_index}"
            for key in ("file", "outcome", "expected", "dag_nodes", "query_shape", "corpus_manifest"):
                require(after.get(key) == before.get(key), f"{label} {key} drift")
            for key in STRUCTURAL_STATS:
                require(
                    after["backend_stats"].get(key) == before["backend_stats"].get(key),
                    f"{label} {key} drift",
                )


def analyze(paths: list[Path], baseline_binary: Path, candidate_binary: Path) -> dict[str, Any]:
    require(len(paths) == len(SCHEDULE), "timing protocol requires 12 artifacts")
    require(sha256(baseline_binary) == BASELINE_BINARY_SHA256, "baseline binary hash drift")
    require(sha256(candidate_binary) == CANDIDATE_BINARY_SHA256, "candidate binary hash drift")
    artifacts = []
    artifact_hashes = []
    config_identity = None
    for index, (path, cell) in enumerate(zip(paths, SCHEDULE, strict=True), start=1):
        artifact, digest = load_json(path)
        validate_artifact(artifact, cell, f"run {index}")
        identity = (
            artifact["config"]["config_hash"],
            artifact["config"]["corpus_hash"],
            artifact["config"]["experiment"]["environment_hash"],
        )
        if config_identity is None:
            config_identity = identity
        require(identity == config_identity, f"run {index} config/environment drift")
        artifacts.append(artifact)
        artifact_hashes.append(digest)
    validate_cross_run_structure(artifacts)
    totals = []
    family_totals = []
    for artifact in artifacts:
        total, families = run_totals(artifact)
        totals.append(total)
        family_totals.append(families)
    baseline_totals = [total for total, cell in zip(totals, SCHEDULE, strict=True) if cell == "B"]
    candidate_totals = [total for total, cell in zip(totals, SCHEDULE, strict=True) if cell == "C"]
    ratios = []
    family_ratios = {family: [] for family in FAMILIES}
    for pair in range(6):
        left = pair * 2
        right = left + 1
        baseline_index = left if SCHEDULE[left] == "B" else right
        candidate_index = right if SCHEDULE[right] == "C" else left
        ratios.append(totals[candidate_index] / totals[baseline_index])
        for family in FAMILIES:
            family_ratios[family].append(
                family_totals[candidate_index][family]
                / family_totals[baseline_index][family]
            )
    ratio_geomean = geometric_mean(ratios)
    bootstrap_upper = exhaustive_bootstrap_upper(ratios)
    baseline_cv = coefficient_of_variation(baseline_totals)
    candidate_cv = coefficient_of_variation(candidate_totals)
    family_geomeans = {
        family: geometric_mean(values) for family, values in family_ratios.items()
    }
    gates = {
        "aggregate_geomean_at_most_0_97": ratio_geomean <= 0.97,
        "bootstrap_upper_below_1": bootstrap_upper < 1.0,
        "baseline_cv_at_most_3_percent": baseline_cv <= 3.0,
        "candidate_cv_at_most_3_percent": candidate_cv <= 3.0,
        "no_family_geomean_above_1_02": max(family_geomeans.values()) <= 1.02,
    }
    return {
        "schema": SCHEMA,
        "accepted": all(gates.values()),
        "schedule": list(SCHEDULE),
        "artifact_sha256": artifact_hashes,
        "binary_sha256": {
            "baseline": BASELINE_BINARY_SHA256,
            "candidate": CANDIDATE_BINARY_SHA256,
        },
        "baseline_total_ms": baseline_totals,
        "candidate_total_ms": candidate_totals,
        "paired_candidate_over_baseline": ratios,
        "paired_geometric_mean": ratio_geomean,
        "exhaustive_bootstrap_95_upper": bootstrap_upper,
        "baseline_cv_percent": baseline_cv,
        "candidate_cv_percent": candidate_cv,
        "family_paired_geometric_means": family_geomeans,
        "gates": gates,
        "complete_correctness_and_structure": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifacts", nargs=12, type=Path)
    parser.add_argument("--baseline-binary", type=Path, required=True)
    parser.add_argument("--candidate-binary", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    report = analyze(args.artifacts, args.baseline_binary, args.candidate_binary)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
