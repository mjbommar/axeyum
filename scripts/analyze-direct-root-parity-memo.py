#!/usr/bin/env python3
"""Validate ADR-0277's fixed direct-root parity-leaf memo experiment."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
CONSTRUCTION_ANALYZER = ROOT / "scripts" / "analyze-cnf-construction-profile.py"
SPEC = importlib.util.spec_from_file_location("cnf_construction_analysis", CONSTRUCTION_ANALYZER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("cannot load CNF construction analyzer")
CNF_ANALYSIS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CNF_ANALYSIS)

SCHEMA = "axeyum.direct-root-parity-memo-analysis.v1"
BASELINE_ARTIFACT_SHA256 = "e61f6a61e168ab87ce111557b703621a7c738387d8018cfa7a34f9e9c556421a"
BASELINE_ANALYSIS_SHA256 = "4dc29c7ce4bd6d5e37956bc5d775bf64ab2fe47be99705959947656cae8c608c"
BASELINE_SOURCE = "6ff05905131b58a8cfa1c15e91ea97c9304f5ead"
CANDIDATE_SOURCE = "900f69973c90c0655dfcfd564fc9b67c44388506"
MANIFEST_SHA256 = "7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064"
FAMILIES = {
    "arithmetic": 36,
    "comparison": 12,
    "mixed": 7,
    "register-slice": 52,
    "slice-partial": 54,
    "trivial": 1,
}
COUNTER_DELTAS = {
    "clause_attempts": -107_000,
    "duplicate_clauses_skipped": -107_000,
    "declared_clause_literals": -321_000,
    "visited_clause_literals": -321_000,
    "false_constants_dropped": -107_000,
    "canonical_literals": -214_000,
    "canonical_binary_clauses": -107_000,
    "primary_occupied_probes": -107_000,
    "primary_exact_duplicates": -107_000,
}
FAMILY_REMOVED_DUPLICATES = {
    "register-slice": 23_828,
    "slice-partial": 83_172,
}
STRUCTURAL_BACKEND_STATS = (
    "aig_nodes",
    "cnf_variables",
    "cnf_clauses",
    "cnf_clauses_emitted",
)
ORIGIN_METRICS = (
    "duplicate_clauses",
    "duplicate_canonical_literals",
    "lengths",
    "participating_instances",
    "largest_single_instance_clauses",
    "families",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as source:
        value = json.load(source)
    require(isinstance(value, dict), f"expected JSON object: {path}")
    return value


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def source_revision(artifact: dict[str, Any]) -> str | None:
    return artifact.get("config", {}).get("experiment", {}).get("source", {}).get("revision")


def counter_deltas(
    baseline: dict[str, int], candidate: dict[str, int]
) -> dict[str, int]:
    require(set(candidate) == set(baseline), "construction counter set drift")
    observed = {key: candidate[key] - baseline[key] for key in sorted(baseline)}
    expected = {key: COUNTER_DELTAS.get(key, 0) for key in sorted(baseline)}
    require(observed == expected, "construction counter delta mismatch")
    return observed


def family_counter_deltas(
    baseline: dict[str, Any], candidate: dict[str, Any]
) -> dict[str, dict[str, int]]:
    require(set(candidate) == set(baseline), "family set drift")
    rendered = {}
    for family in sorted(baseline):
        before = baseline[family]
        after = candidate[family]
        for key in ("instances", "sat", "unsat"):
            require(after[key] == before[key], f"{family} {key} drift")
        removed = FAMILY_REMOVED_DUPLICATES.get(family, 0)
        expected = {
            key: (COUNTER_DELTAS.get(key, 0) * removed // 107_000)
            for key in before["counters"]
        }
        observed = {
            key: after["counters"][key] - before["counters"][key]
            for key in before["counters"]
        }
        require(observed == expected, f"{family} construction delta mismatch")
        rendered[family] = observed
    return rendered


def origin_core(row: dict[str, Any]) -> tuple[Any, ...]:
    return (
        row["first_origin"],
        row["duplicate_origin"],
        row["owner_relation"],
        *(row[key] for key in ORIGIN_METRICS),
    )


def selected_origin(row: dict[str, Any]) -> bool:
    parity = "root/and_tree/forward/parity"
    return (
        row.get("first_origin") == parity
        and row.get("duplicate_origin") == parity
        and row.get("owner_relation") == "same"
    )


def validate_instances(
    baseline: dict[str, Any], candidate: dict[str, Any]
) -> None:
    before = baseline.get("instances")
    after = candidate.get("instances")
    require(isinstance(before, list) and isinstance(after, list), "artifact instances missing")
    require(len(before) == len(after) == 162, "artifact instance population drift")
    for index, (base_row, candidate_row) in enumerate(zip(before, after, strict=True)):
        label = f"instance[{index}]"
        for key in ("file", "outcome", "expected", "dag_nodes", "query_shape"):
            require(candidate_row.get(key) == base_row.get(key), f"{label} {key} drift")
        require(
            candidate_row.get("corpus_manifest") == base_row.get("corpus_manifest"),
            f"{label} manifest drift",
        )
        before_stats = base_row.get("backend_stats", {})
        after_stats = candidate_row.get("backend_stats", {})
        for key in STRUCTURAL_BACKEND_STATS:
            require(after_stats.get(key) == before_stats.get(key), f"{label} {key} drift")


def analyze(
    baseline_artifact: dict[str, Any],
    baseline_analysis: dict[str, Any],
    candidate_artifact: dict[str, Any],
) -> dict[str, Any]:
    require(source_revision(baseline_artifact) == BASELINE_SOURCE, "baseline source drift")
    require(source_revision(candidate_artifact) == CANDIDATE_SOURCE, "candidate source drift")
    for key in ("config_hash", "corpus_hash"):
        require(
            candidate_artifact["config"].get(key) == baseline_artifact["config"].get(key),
            f"{key} drift",
        )
    require(
        candidate_artifact["config"]["experiment"].get("environment_hash")
        == baseline_artifact["config"]["experiment"].get("environment_hash"),
        "environment hash drift",
    )
    candidate_report = CNF_ANALYSIS.analyze_artifact(
        candidate_artifact,
        expected_files=162,
        expected_sat=88,
        expected_unsat=74,
        expected_manifest_sha256=MANIFEST_SHA256,
        expected_families=FAMILIES,
    )
    require(baseline_analysis.get("accepted") is True, "baseline analysis is not accepted")
    require(
        baseline_analysis.get("schema") == "axeyum.cnf-construction-profile-analysis.v3",
        "baseline analysis schema drift",
    )
    aggregate_delta = counter_deltas(
        baseline_analysis["aggregate"], candidate_report["aggregate"]
    )
    family_delta = family_counter_deltas(
        baseline_analysis["families"], candidate_report["families"]
    )
    baseline_rows = baseline_analysis["duplicate_origins"]["rows"]
    selected_rows = [row for row in baseline_rows if selected_origin(row)]
    require(len(selected_rows) == 1, "baseline selected-origin cardinality drift")
    selected = selected_rows[0]
    require(selected["duplicate_clauses"] == 107_000, "baseline selected-origin total drift")
    require(selected["duplicate_canonical_literals"] == 214_000, "baseline selected-origin literal drift")
    remaining = sorted(origin_core(row) for row in baseline_rows if not selected_origin(row))
    candidate_rows = sorted(
        origin_core(row) for row in candidate_report["duplicate_origins"]["rows"]
    )
    require(candidate_rows == remaining, "nonselected duplicate-origin row drift")
    require(
        candidate_report["duplicate_origins"]["duplicate_clauses"] == 12_260,
        "candidate duplicate total mismatch",
    )
    overlap = candidate_report["duplicate_origins"]["parity_overlap"]
    require(overlap["available"] is True, "candidate parity profile is unavailable")
    require(overlap["duplicate_clauses"] == 0 and overlap["rows"] == [], "parity overlap remains")
    validate_instances(baseline_artifact, candidate_artifact)
    return {
        "schema": SCHEMA,
        "accepted": True,
        "baseline_source": BASELINE_SOURCE,
        "candidate_source": CANDIDATE_SOURCE,
        "population": candidate_report["population"],
        "aggregate_delta": aggregate_delta,
        "family_counter_deltas": family_delta,
        "candidate_duplicate_clauses": candidate_report["duplicate_origins"][
            "duplicate_clauses"
        ],
        "candidate_parity_overlap_clauses": overlap["duplicate_clauses"],
        "nonselected_origin_rows_preserved": True,
        "per_instance_structure_preserved": True,
        "timing_authorized": True,
        "claim_limits": [
            "Profiled timing is diagnostic.",
            "The structural gate authorizes only ADR-0277's registered unprofiled timing protocol.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-artifact", type=Path, required=True)
    parser.add_argument("--baseline-analysis", type=Path, required=True)
    parser.add_argument("--candidate-artifact", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    require(
        sha256(args.baseline_artifact) == BASELINE_ARTIFACT_SHA256,
        "baseline artifact hash mismatch",
    )
    require(
        sha256(args.baseline_analysis) == BASELINE_ANALYSIS_SHA256,
        "baseline analysis hash mismatch",
    )
    report = analyze(
        load_json(args.baseline_artifact),
        load_json(args.baseline_analysis),
        load_json(args.candidate_artifact),
    )
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
