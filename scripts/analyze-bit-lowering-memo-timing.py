#!/usr/bin/env python3
"""Validate and score ADR-0300's fixed unprofiled timing protocol."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import statistics
from pathlib import Path
from typing import Any


SCHEMA = "axeyum.bit-lowering-memo-timing-analysis.v1"
SCHEDULE = ("B", "C", "C", "B", "B", "C", "C", "B", "B", "C", "C", "B")
BASELINE_SOURCE = "d13d1f92446e86113702a7cc27d3e1a5eb67c687"
CANDIDATE_SOURCE = "2c9209fe9c4442cf87b6c121a04997849c05930b"
BASELINE_BINARY_SHA256 = "65d819528f10645042103275e4c79904e47f377326dc9e1159f8c36d8795c515"
CANDIDATE_BINARY_SHA256 = "06d417ef0e0082be87c4a311b5bc92a3a669d5accde5dbd27a349f78f1c93377"
MANIFEST_SHA256 = "sha256:7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064"
FAMILIES = (
    "arithmetic",
    "comparison",
    "mixed",
    "register-slice",
    "slice-partial",
    "trivial",
)
STRUCTURAL_STATS = (
    "aig_inputs",
    "aig_nodes",
    "aig_and_requests",
    "aig_and_trivial_simplifications",
    "aig_and_absorption_simplifications",
    "aig_and_structural_hash_hits",
    "aig_and_nodes_created",
    "cnf_variables",
    "cnf_clauses",
    "cnf_clause_attempts",
    "cnf_clauses_emitted",
    "cnf_direct_root_nodes",
    "cnf_duplicate_clauses_skipped",
    "cnf_tautological_clauses_skipped",
    "cnf_reachable_nodes",
    "cnf_skipped_helper_nodes",
    "cnf_and_tree_gates",
    "cnf_binary_and_gates",
    "cnf_not_and_gates",
    "cnf_not_ite_gates",
    "cnf_xor_gates",
)
STABLE_INSTANCE_FIELDS = (
    "file",
    "outcome",
    "expected",
    "assertions",
    "dag_nodes",
    "tree_nodes",
    "distinct_symbols",
    "max_depth",
    "query_plan",
    "query_shape",
    "corpus_manifest",
    "rewrite",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def load_json(path: Path) -> dict[str, Any]:
    def reject_nonfinite(token: str) -> None:
        raise RuntimeError(f"non-finite JSON value {token}: {path}")

    value = json.loads(path.read_bytes(), parse_constant=reject_nonfinite)
    require(isinstance(value, dict), f"expected JSON object: {path}")
    return value


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def geometric_mean(values: list[float]) -> float:
    require(
        values and all(value > 0.0 and math.isfinite(value) for value in values),
        "invalid ratio",
    )
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


def validate_artifact(artifact: dict[str, Any], cell: str, label: str) -> None:
    require(artifact.get("version") == 39, f"{label} artifact version drift")
    config = artifact.get("config", {})
    summary = artifact.get("summary", {})
    instances = artifact.get("instances")
    expected_source = BASELINE_SOURCE if cell == "B" else CANDIDATE_SOURCE
    require(config.get("backend_kind") == "sat-bv", f"{label} backend drift")
    require(config.get("logic") == "QF_BV", f"{label} logic drift")
    require(config.get("jobs") == 1, f"{label} worker drift")
    require(config.get("profile_bit_demand") is False, f"{label} is memo-profiled")
    require(config.get("profile_cnf_construction") is False, f"{label} is CNF-profiled")
    require(config.get("preprocess") is False, f"{label} preprocess drift")
    require(config.get("rewrite", {}).get("mode") == "off", f"{label} rewrite drift")
    require(config.get("require_reproducible_run") is True, f"{label} reproducibility gate absent")
    require(config.get("require_deterministic_resources") is True, f"{label} resource gate absent")
    require(config.get("require_in_process_z3") is True, f"{label} Z3 gate absent")
    require(config.get("compare_z3") is True, f"{label} Z3 comparison absent")
    require(config.get("timeout_ms") == 10_000, f"{label} timeout drift")
    require(config.get("resource_limit") == 2_000_000, f"{label} resource drift")
    require(config.get("node_budget") == 300_000, f"{label} node budget drift")
    require(config.get("cnf_variable_budget") == 3_000_000, f"{label} CNF var drift")
    require(config.get("cnf_clause_budget") == 8_000_000, f"{label} CNF clause drift")
    require(config.get("corpus_manifest", {}).get("content_hash") == MANIFEST_SHA256, f"{label} manifest drift")
    source = config.get("experiment", {}).get("source", {})
    require(source.get("revision") == expected_source, f"{label} source drift")
    require(source.get("dirty") is False, f"{label} source is dirty")
    require(isinstance(instances, list) and len(instances) == 162, f"{label} instance count drift")
    require(summary.get("files") == 162, f"{label} file count drift")
    require(summary.get("sat") == 88 and summary.get("unsat") == 74, f"{label} verdict count drift")
    for key in ("unknown", "unsupported", "errors", "disagree", "model_replay_failures"):
        require(summary.get(key) == 0, f"{label} summary.{key} is nonzero")
    require(summary.get("manifest", {}).get("agree") == 162, f"{label} manifest disagreement")
    require(summary.get("oracle", {}).get("agree") == 162, f"{label} oracle disagreement")
    require(summary.get("oracle", {}).get("skipped") == 0, f"{label} oracle skip")
    require(summary.get("layer_attribution", {}).get("model_replay_instances") == 88, f"{label} replay population drift")
    memo = summary.get("layer_attribution", {}).get("bit_lowering_memo", {})
    require(memo.get("profile_complete") is False, f"{label} memo profile leaked into timing")
    require(memo.get("representation_counts", {}).get("unavailable") == 162, f"{label} memo representation leak")
    for index, instance in enumerate(instances):
        stats = instance.get("backend_stats", {})
        require(stats.get("bit_lowering_memo_profile_complete") == 0.0, f"{label} row {index} memo profile leak")
        require(stats.get("bit_lowering_memo_representation") == 0.0, f"{label} row {index} memo representation leak")


def validate_cross_run_structure(artifacts: list[dict[str, Any]]) -> None:
    reference = artifacts[0]["instances"]
    for run_index, artifact in enumerate(artifacts[1:], start=2):
        for instance_index, (before, after) in enumerate(
            zip(reference, artifact["instances"], strict=True)
        ):
            label = f"run {run_index} instance {instance_index}"
            for key in STABLE_INSTANCE_FIELDS:
                require(after.get(key) == before.get(key), f"{label} {key} drift")
            for key in STRUCTURAL_STATS:
                require(
                    after["backend_stats"].get(key) == before["backend_stats"].get(key),
                    f"{label} {key} drift",
                )


def run_metrics(
    artifact: dict[str, Any], timing: dict[str, Any], cell: str
) -> dict[str, Any]:
    require(timing.get("exit_status") == 0, "timed process did not exit successfully")
    rss = timing.get("max_rss_kib")
    require(isinstance(rss, int) and 0 < rss <= 4 * 1024 * 1024, "invalid max RSS")
    elapsed = timing.get("elapsed_seconds")
    require(isinstance(elapsed, (int, float)) and elapsed > 0, "invalid elapsed time")
    bit_blast = 0.0
    cold_total = 0.0
    families = {family: 0.0 for family in FAMILIES}
    for instance in artifact["instances"]:
        bit_value = float(instance["backend_stats"]["bit_blast_ms"])
        cold_value = float(instance["cold_total_ms"])
        require(bit_value > 0.0 and math.isfinite(bit_value), "invalid bit-blast time")
        require(cold_value > 0.0 and math.isfinite(cold_value), "invalid cold-total time")
        family = instance["corpus_manifest"]["family"]
        require(family in families, "unknown family")
        bit_blast += bit_value
        cold_total += cold_value
        families[family] += bit_value
    return {
        "cell": cell,
        "bit_blast_ms": bit_blast,
        "cold_total_ms": cold_total,
        "family_bit_blast_ms": families,
        "max_rss_kib": rss,
        "elapsed_seconds": float(elapsed),
    }


def evaluate_metrics(runs: list[dict[str, Any]]) -> dict[str, Any]:
    require(len(runs) == 12, "timing protocol requires 12 runs")
    require(tuple(run["cell"] for run in runs) == SCHEDULE, "schedule drift")
    baseline = [run for run in runs if run["cell"] == "B"]
    candidate = [run for run in runs if run["cell"] == "C"]
    bit_ratios: list[float] = []
    cold_ratios: list[float] = []
    rss_ratios: list[float] = []
    family_ratios = {family: [] for family in FAMILIES}
    for pair in range(6):
        left = runs[pair * 2]
        right = runs[pair * 2 + 1]
        before = left if left["cell"] == "B" else right
        after = right if right["cell"] == "C" else left
        bit_ratios.append(after["bit_blast_ms"] / before["bit_blast_ms"])
        cold_ratios.append(after["cold_total_ms"] / before["cold_total_ms"])
        rss_ratios.append(after["max_rss_kib"] / before["max_rss_kib"])
        for family in FAMILIES:
            family_ratios[family].append(
                after["family_bit_blast_ms"][family]
                / before["family_bit_blast_ms"][family]
            )
    family_geomeans = {
        family: geometric_mean(values) for family, values in family_ratios.items()
    }
    baseline_family_means = {
        family: statistics.fmean(run["family_bit_blast_ms"][family] for run in baseline)
        for family in FAMILIES
    }
    gated_families = [
        family for family in FAMILIES if baseline_family_means[family] >= 5.0
    ]
    bit_geomean = geometric_mean(bit_ratios)
    bit_bootstrap_upper = exhaustive_bootstrap_upper(bit_ratios)
    cold_geomean = geometric_mean(cold_ratios)
    cold_bootstrap_upper = exhaustive_bootstrap_upper(cold_ratios)
    gates = {
        "bit_blast_geomean_at_most_0_97": bit_geomean <= 0.97,
        "bit_blast_bootstrap_upper_below_1": bit_bootstrap_upper < 1.0,
        "baseline_bit_blast_cv_at_most_3_percent": coefficient_of_variation(
            [run["bit_blast_ms"] for run in baseline]
        )
        <= 3.0,
        "candidate_bit_blast_cv_at_most_3_percent": coefficient_of_variation(
            [run["bit_blast_ms"] for run in candidate]
        )
        <= 3.0,
        "gated_family_geomeans_at_most_1_02": all(
            family_geomeans[family] <= 1.02 for family in gated_families
        ),
        "cold_total_geomean_at_most_1": cold_geomean <= 1.0,
        "cold_total_bootstrap_upper_at_most_1_02": cold_bootstrap_upper <= 1.02,
        "every_paired_rss_ratio_at_most_1_05": max(rss_ratios) <= 1.05,
    }
    return {
        "accepted": all(gates.values()),
        "schedule": list(SCHEDULE),
        "baseline_bit_blast_ms": [run["bit_blast_ms"] for run in baseline],
        "candidate_bit_blast_ms": [run["bit_blast_ms"] for run in candidate],
        "paired_bit_blast_candidate_over_baseline": bit_ratios,
        "bit_blast_paired_geometric_mean": bit_geomean,
        "bit_blast_exhaustive_bootstrap_95_upper": bit_bootstrap_upper,
        "baseline_bit_blast_cv_percent": coefficient_of_variation(
            [run["bit_blast_ms"] for run in baseline]
        ),
        "candidate_bit_blast_cv_percent": coefficient_of_variation(
            [run["bit_blast_ms"] for run in candidate]
        ),
        "paired_cold_total_candidate_over_baseline": cold_ratios,
        "cold_total_paired_geometric_mean": cold_geomean,
        "cold_total_exhaustive_bootstrap_95_upper": cold_bootstrap_upper,
        "paired_rss_candidate_over_baseline": rss_ratios,
        "maximum_paired_rss_ratio": max(rss_ratios),
        "baseline_family_mean_bit_blast_ms": baseline_family_means,
        "family_paired_geometric_means": family_geomeans,
        "gated_families": gated_families,
        "gates": gates,
    }


def analyze(run_root: Path, baseline_binary: Path, candidate_binary: Path) -> dict[str, Any]:
    require(sha256(baseline_binary) == BASELINE_BINARY_SHA256, "baseline binary hash drift")
    require(sha256(candidate_binary) == CANDIDATE_BINARY_SHA256, "candidate binary hash drift")
    manifest = load_json(run_root / "run-manifest.json")
    require(manifest.get("schedule") == list(SCHEDULE), "run manifest schedule drift")
    require(manifest.get("baseline_source") == BASELINE_SOURCE, "run manifest baseline drift")
    require(manifest.get("candidate_source") == CANDIDATE_SOURCE, "run manifest candidate drift")
    require(
        manifest.get("baseline_binary_sha256") == BASELINE_BINARY_SHA256,
        "run manifest baseline binary drift",
    )
    require(
        manifest.get("candidate_binary_sha256") == CANDIDATE_BINARY_SHA256,
        "run manifest candidate binary drift",
    )
    manifest_runs = manifest.get("runs")
    require(isinstance(manifest_runs, list) and len(manifest_runs) == 12, "run manifest population drift")
    artifacts: list[dict[str, Any]] = []
    metrics: list[dict[str, Any]] = []
    artifact_hashes: list[str] = []
    config_identity = None
    for index, cell in enumerate(SCHEDULE, start=1):
        run_dir = run_root / f"run-{index:02d}-{cell}"
        manifest_run = manifest_runs[index - 1]
        require(
            manifest_run
            == {
                "index": index,
                "cell": cell,
                "artifact": f"run-{index:02d}-{cell}/artifact.json",
                "time": f"run-{index:02d}-{cell}/time.json",
            },
            f"run manifest entry {index} drift",
        )
        artifact_path = run_dir / "artifact.json"
        artifact = load_json(artifact_path)
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
        metrics.append(run_metrics(artifact, load_json(run_dir / "time.json"), cell))
        artifact_hashes.append(sha256(artifact_path))
    validate_cross_run_structure(artifacts)
    result = evaluate_metrics(metrics)
    result.update(
        {
            "schema": SCHEMA,
            "artifact_sha256": artifact_hashes,
            "binary_sha256": {
                "baseline": BASELINE_BINARY_SHA256,
                "candidate": CANDIDATE_BINARY_SHA256,
            },
            "complete_correctness_and_structure": True,
        }
    )
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-root", type=Path, required=True)
    parser.add_argument("--baseline-binary", type=Path, required=True)
    parser.add_argument("--candidate-binary", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    report = analyze(args.run_root, args.baseline_binary, args.candidate_binary)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
