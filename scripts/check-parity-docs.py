#!/usr/bin/env python3
"""Fail when live parity documentation contradicts committed measurements.

This is intentionally a narrow guard, not a natural-language fact checker.  It
owns the claims that have already rotted repeatedly: the generated division
totals, exact dominance-audit denominators, the paired 20-second p4dfa control,
the reviewer-facing project-state summary, and the source/test-backed
categorical-engine maturity classification. New guarded numerical claims should
be added only when they have one canonical, machine-readable artifact; the
categorical markers guard the dated audit and the live roadmap language that
points to it.
"""

from __future__ import annotations

import glob
import importlib.util
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
GEN_SCOREBOARD = ROOT / "scripts" / "gen-scoreboard.py"
GAP_DOC = ROOT / "docs" / "plan" / "gap-analysis-z3-lean-2026-07-21.md"
PROJECT_STATE = ROOT / "docs" / "PROJECT-STATE.md"
BENCHMARK_GUIDE = ROOT / "docs" / "user-guide" / "benchmarks.md"
CATEGORICAL_AUDIT = (
    ROOT / "docs" / "plan" / "categorical-engine-depth-audit-2026-07-21.md"
)
CI_WORKFLOW = ROOT / ".github" / "workflows" / "ci.yml"
AXEYUM_P4DFA = (
    ROOT
    / "bench-results"
    / "baselines"
    / "qf-bv-p4dfa-axeyum-vs-z3-20s-authoritative.json"
)
Z3_P4DFA = (
    ROOT
    / "bench-results"
    / "baselines"
    / "qf-bv-p4dfa-z3-standalone-20s.json"
)
SMTCOMP_INVENTORY = (
    ROOT / "bench-results" / "smtcomp-repro-20260721" / "inventory.json"
)
SMTCOMP_QFBV = (
    ROOT / "bench-results" / "smtcomp-repro-20260721" / "head_to_head_qfbv.json"
)
SMTCOMP_PROVENANCE = (
    ROOT / "bench-results" / "smtcomp-repro-20260721" / "provenance.json"
)
MEASUREMENT_PROVENANCE = (
    ROOT / "docs" / "plan" / "generated" / "measurement-provenance-matrix.json"
)

LIVE_DOCS = (
    ROOT / "README.md",
    ROOT / "PLAN.md",
    ROOT / "STATUS.md",
    ROOT / "bench-results" / "SCOREBOARD.md",
    ROOT / "docs" / "README.md",
    PROJECT_STATE,
    ROOT / "docs" / "plan" / "README.md",
    ROOT / "docs" / "user-guide" / "benchmarks.md",
    ROOT / "docs" / "user-guide" / "limitations.md",
    GAP_DOC,
    CATEGORICAL_AUDIT,
    ROOT / "docs" / "plan" / "01-dependency-dag.md",
    ROOT / "docs" / "plan" / "track-3-proof-lean" / "P3.8-interpolation.md",
    ROOT / "docs" / "plan" / "track-4-usecases-frontend" / "README.md",
    ROOT / "docs" / "plan" / "track-4-usecases-frontend" / "P4.6-chc-horn.md",
    ROOT / "docs" / "plan" / "track-4-usecases-frontend" / "P4.7-synthesis.md",
    ROOT / "docs" / "research" / "08-planning" / "roadmap.md",
)

PUBLIC_CLAIM_DOCS = (
    ROOT / "README.md",
    ROOT / "docs" / "README.md",
    PROJECT_STATE,
    ROOT / "docs" / "user-guide" / "benchmarks.md",
    ROOT / "docs" / "user-guide" / "limitations.md",
)

STALE_PATTERNS = (
    re.compile(r"Z3 (?:still )?decides all 113", re.IGNORECASE),
    re.compile(r"Z3\s+113/113", re.IGNORECASE),
    re.compile(r"p4dfa 113, parity, both hard-capped", re.IGNORECASE),
    re.compile(r"~15/35 rows"),
    re.compile(r"\b19/35 decide-strong\b"),
    re.compile(r"\b23 fragments\b"),
    re.compile(r"\b~73%\b"),
    re.compile(r"new categorical engines", re.IGNORECASE),
    re.compile(r"biggest categorical gap", re.IGNORECASE),
    re.compile(r"categorically-missing", re.IGNORECASE),
    re.compile(r"T3\.8\.5 façade — DONE"),
    re.compile(r"8[–-]8\s*@20s,\s*11[–-]11\s*@60s", re.IGNORECASE),
    re.compile(r"parity is \*budget-robust\*", re.IGNORECASE),
    re.compile(r"\|\s*20 s\s*\|\s*8 / 113\s*\|\s*9 / 113\s*\|", re.IGNORECASE),
)

PUBLIC_STALE_PATTERNS = (
    re.compile(r"every\s+`unsat`\s+carries", re.IGNORECASE),
    re.compile(r"It is sound \(`unknown`, never a wrong", re.IGNORECASE),
)


def load_scoreboard_module():
    spec = importlib.util.spec_from_file_location("axeyum_gen_scoreboard", GEN_SCOREBOARD)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {GEN_SCOREBOARD}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def decided(summary: dict) -> int:
    return int(summary.get("sat", 0)) + int(summary.get("unsat", 0))


def measured_snapshot() -> dict[str, int]:
    scoreboard = load_scoreboard_module()
    rows = scoreboard.load_division_baselines() + scoreboard.load_synthetic_baselines()

    audits = []
    for path in sorted(glob.glob(str(ROOT / "bench-results" / "dominance" / "*.json"))):
        audit = load_json(Path(path))
        if audit.get("complete_audit"):
            audits.append(audit)

    axeyum = load_json(AXEYUM_P4DFA)
    z3 = load_json(Z3_P4DFA)
    inventory = load_json(SMTCOMP_INVENTORY)
    qfbv = load_json(SMTCOMP_QFBV)
    provenance = load_json(SMTCOMP_PROVENANCE)
    measurement = load_json(MEASUREMENT_PROVENANCE)
    measurement_score = measurement["summary"]["regression_scoreboard"]
    measurement_public = measurement["summary"]["public_inventory"]
    measurement_overlap = measurement["summary"]["cross_regime"]
    for artifact in (axeyum, z3):
        config = artifact["config"]
        summary = artifact["summary"]
        if config["timeout_ms"] != 20_000 or summary["files"] != 113:
            raise RuntimeError("p4dfa control is no longer the registered 113-file/20-second cell")
    if axeyum["config"]["corpus_hash"] != z3["config"]["corpus_hash"]:
        raise RuntimeError("p4dfa Axeyum/Z3 controls do not bind the same corpus hash")
    qfbv_division = qfbv["divisions"]["QF_BV"]
    qfbv_solvers = qfbv_division["solvers"]

    baseline_unsat_instances = [
        instance
        for audit in audits
        for instance in audit["instances"]
        if instance.get("baseline_outcome") == "unsat"
    ]

    dominant_unsat = sum(
        instance.get("audit_outcome") == "unsat"
        and instance.get("evidence_certified") is True
        and instance.get("evidence_checked") is True
        and instance.get("lean_checked") is True
        and not instance.get("trust_holes")
        for instance in baseline_unsat_instances
    )
    uncertified_unsat = sum(
        instance.get("audit_outcome") == "unsat"
        and instance.get("evidence_certified") is not True
        for instance in baseline_unsat_instances
    )
    lean_reconstruction_gap = sum(
        instance.get("audit_outcome") == "unsat"
        and instance.get("evidence_certified") is True
        and instance.get("evidence_checked") is True
        and instance.get("lean_checked") is not True
        and not instance.get("trust_holes")
        for instance in baseline_unsat_instances
    )
    proof_production_errors = sum(
        instance.get("audit_outcome") != "unsat"
        for instance in baseline_unsat_instances
    )

    scoreboard_ids = []
    scoreboard_aggregate_only = 0
    for row in rows:
        baseline = load_json(ROOT / row["file"])
        instances = baseline.get("instances", [])
        if not instances:
            scoreboard_aggregate_only += row["files"]
            continue
        for instance in instances:
            path = instance["file"]
            if "non-incremental/" in path:
                path = path.split("non-incremental/", 1)[1]
            elif "quantified/" in path:
                path = "quantified/" + path.split("quantified/", 1)[1]
            scoreboard_ids.append(path)

    return {
        "rows": len(rows),
        "logics": len({row["logic"] for row in rows}),
        "files": sum(row["files"] for row in rows),
        "decided": sum(row["decided"] for row in rows),
        "compared": sum(row["compared"] for row in rows),
        "disagree": sum(row["disagree"] for row in rows),
        "decide_strong_rows": sum(row["decide_pct"] >= 80.0 for row in rows),
        "complete_audits": len(audits),
        "fully_dominant_rows": sum(
            audit["summary"].get("dominant_pct_audited") == 100.0
            for audit in audits
        ),
        "dominant_decisions": sum(
            audit["summary"]["dominant_candidates"] for audit in audits
        ),
        "audited_decisions": sum(
            audit["summary"]["audited_decided"] for audit in audits
        ),
        "lean_checked_unsat": sum(
            audit["summary"]["lean_checked_unsat"] for audit in audits
        ),
        "certified_unsat": sum(
            instance.get("evidence_certified") is True
            for instance in baseline_unsat_instances
        ),
        "audit_reported_checked_unsat": sum(
            instance.get("evidence_checked") is True
            for instance in baseline_unsat_instances
        ),
        "independently_checked_unsat": sum(
            instance.get("evidence_certified") is True
            and instance.get("evidence_checked") is True
            for instance in baseline_unsat_instances
        ),
        # The historical summary field counts baseline UNSAT decisions, including
        # proof-production failures. Keep both denominators explicit so a failed
        # evidence audit cannot be described as an audited UNSAT result.
        "baseline_unsat": sum(
            audit["summary"]["audited_unsat"] for audit in audits
        ),
        "audit_reproduced_unsat": sum(
            instance.get("audit_outcome") == "unsat"
            for audit in audits
            for instance in audit["instances"]
        ),
        "dominant_unsat": dominant_unsat,
        "uncertified_unsat": uncertified_unsat,
        "lean_reconstruction_gap": lean_reconstruction_gap,
        "proof_production_errors": proof_production_errors,
        "p4dfa_axeyum_20s": decided(axeyum["summary"]),
        "p4dfa_z3_20s": decided(z3["summary"]),
        "public_inventory_files": inventory["aggregate"]["total"],
        "public_inventory_decided": inventory["aggregate"]["decided_correct"],
        "public_inventory_declined": inventory["aggregate"]["declined"],
        "public_inventory_wrong": inventory["aggregate"]["WRONG"],
        "public_inventory_no_answer": inventory["aggregate"]["no_answer"],
        "qfbv_head_to_head_files": qfbv_division["n_benchmarks"],
        "qfbv_head_to_head_axeyum": qfbv_solvers["axeyum"]["par2"]["n"],
        "qfbv_head_to_head_cvc5": qfbv_solvers["cvc5"]["par2"]["n"],
        "qfbv_head_to_head_bitwuzla": qfbv_solvers["bitwuzla"]["par2"]["n"],
        "scoreboard_file_occurrences": len(scoreboard_ids),
        "scoreboard_unique_ids": len(set(scoreboard_ids)),
        "scoreboard_repeated_occurrences": len(scoreboard_ids)
        - len(set(scoreboard_ids)),
        "scoreboard_aggregate_only": scoreboard_aggregate_only,
        "public_source_families": provenance["summary"]["source_families"],
        "public_unique_sha256": provenance["summary"]["unique_content_sha256"],
        "public_exact_duplicate_groups": provenance["summary"]["exact_duplicate_groups"],
        "scoreboard_unique_sha256": measurement_score["unique_content_sha256"],
        "scoreboard_exact_duplicate_groups": measurement_score["exact_duplicate_groups"],
        "scoreboard_exact_duplicate_excess": measurement_score["exact_duplicate_excess"],
        "cross_regime_unique_overlap": measurement_overlap["unique_content_overlap"],
        "neutral_measurement_rows": measurement_score["neutral_oracle_rows"]
        + measurement_public["neutral_oracle_rows"],
    }


def main() -> int:
    snapshot = measured_snapshot()
    failures: list[str] = []

    for path in LIVE_DOCS:
        text = path.read_text(encoding="utf-8")
        for pattern in STALE_PATTERNS:
            if match := pattern.search(text):
                line = text.count("\n", 0, match.start()) + 1
                failures.append(f"{path.relative_to(ROOT)}:{line}: stale parity claim: {match.group(0)!r}")

    for path in PUBLIC_CLAIM_DOCS:
        text = path.read_text(encoding="utf-8")
        for pattern in PUBLIC_STALE_PATTERNS:
            if match := pattern.search(text):
                line = text.count("\n", 0, match.start()) + 1
                failures.append(
                    f"{path.relative_to(ROOT)}:{line}: stale public claim: {match.group(0)!r}"
                )

    required_gap_markers = (
        f"{snapshot['decided']} / {snapshot['files']}",
        f"{snapshot['compared']} oracle-compared",
        f"{snapshot['decide_strong_rows']} / {snapshot['rows']} rows",
        f"{snapshot['fully_dominant_rows']} / {snapshot['complete_audits']} audited rows",
        f"{snapshot['dominant_decisions']} / {snapshot['audited_decisions']} decisions",
        f"{snapshot['baseline_unsat']} baseline `unsat` decisions",
        f"{snapshot['audit_reproduced_unsat']} evidence-audit `unsat` outcomes",
        f"{snapshot['certified_unsat']} certified outcomes",
        f"{snapshot['independently_checked_unsat']} independently checked outcomes",
        f"{snapshot['audit_reported_checked_unsat'] - snapshot['independently_checked_unsat']} vacuous `bare-unsat` check results",
        f"{snapshot['lean_checked_unsat']} Lean-checked outcomes",
        f"{snapshot['p4dfa_axeyum_20s']} / 113",
        f"{snapshot['p4dfa_z3_20s']} / 113",
        f"{snapshot['public_inventory_decided']} / {snapshot['public_inventory_files']}",
        f"{snapshot['public_inventory_wrong']} wrong verdicts",
        f"{snapshot['qfbv_head_to_head_axeyum']} / {snapshot['qfbv_head_to_head_files']}",
        f"{snapshot['scoreboard_file_occurrences']} file-backed occurrences",
        f"{snapshot['scoreboard_unique_ids']} unique normalized benchmark paths",
        f"{snapshot['scoreboard_repeated_occurrences']} repeated occurrences",
        f"{snapshot['scoreboard_aggregate_only']} aggregate-only synthetic cases",
        f"{snapshot['public_source_families']} source families",
        f"{snapshot['public_exact_duplicate_groups']} exact byte-duplicate groups",
        f"{snapshot['scoreboard_unique_sha256']} unique byte contents",
        f"{snapshot['scoreboard_exact_duplicate_groups']} exact-alias groups",
        f"{snapshot['cross_regime_unique_overlap']} contents overlap",
        f"{snapshot['neutral_measurement_rows']} neutral-oracle rows",
    )
    gap_text = GAP_DOC.read_text(encoding="utf-8")
    for marker in required_gap_markers:
        if marker not in gap_text:
            failures.append(f"{GAP_DOC.relative_to(ROOT)}: missing measured marker {marker!r}")

    project_state_markers = (
        f"{snapshot['decided']} / {snapshot['files']}",
        f"{snapshot['compared']} oracle-compared",
        f"{snapshot['disagree']} recorded disagreements",
        f"{snapshot['decide_strong_rows']} / {snapshot['rows']}",
        f"{snapshot['fully_dominant_rows']} / {snapshot['complete_audits']}",
        f"{snapshot['scoreboard_file_occurrences']} occurrences",
        f"{snapshot['scoreboard_unique_ids']} unique normalized paths",
        f"{snapshot['scoreboard_unique_sha256']} unique byte contents",
        f"{snapshot['scoreboard_exact_duplicate_groups']} exact-alias groups",
        f"{snapshot['scoreboard_exact_duplicate_excess']} additional path",
        f"{snapshot['cross_regime_unique_overlap']} exact contents",
        f"{snapshot['public_inventory_decided']} / {snapshot['public_inventory_files']}",
        f"{snapshot['public_inventory_declined']} explicit declines",
        f"{snapshot['public_inventory_no_answer']} no-answer outcomes",
        f"{snapshot['public_inventory_wrong']} wrong verdicts",
        f"{snapshot['dominant_unsat']} / {snapshot['baseline_unsat']}",
        f"{snapshot['uncertified_unsat']} uncertified",
        f"{snapshot['lean_reconstruction_gap']} certified",
        f"{snapshot['proof_production_errors']} proof-production errors",
        f"{snapshot['p4dfa_axeyum_20s']} / 113",
        f"{snapshot['qfbv_head_to_head_axeyum']} / {snapshot['qfbv_head_to_head_files']}",
        "zero interactive textual-session rows",
    )
    project_state_text = PROJECT_STATE.read_text(encoding="utf-8")
    for marker in project_state_markers:
        if marker not in project_state_text:
            failures.append(
                f"{PROJECT_STATE.relative_to(ROOT)}: missing measured marker {marker!r}"
            )

    benchmark_text = BENCHMARK_GUIDE.read_text(encoding="utf-8")
    for marker in (
        f"{snapshot['scoreboard_file_occurrences']} file occurrences",
        f"{snapshot['scoreboard_unique_ids']} normalized paths",
        f"{snapshot['scoreboard_unique_sha256']} exact byte contents",
        f"{snapshot['cross_regime_unique_overlap']} contents occur",
        "43.4% of the public inventory",
        "do not average them",
        "`CARGO_BUILD_JOBS=1`",
    ):
        if marker not in benchmark_text:
            failures.append(
                f"{BENCHMARK_GUIDE.relative_to(ROOT)}: missing measured marker {marker!r}"
            )

    categorical_text = CATEGORICAL_AUDIT.read_text(encoding="utf-8")
    for marker in (
        "125 / 125 passed",
        "94 tests",
        "Horn 22",
        "abduction nine",
        "General SyGuS",
        "No SMT-LIB `get-interpolant`",
        "No SMT-LIB `declare-rel`/`rule`/`query`",
        "No SMT-LIB `get-abduct`",
    ):
        if marker not in categorical_text:
            failures.append(
                f"{CATEGORICAL_AUDIT.relative_to(ROOT)}: missing categorical marker {marker!r}"
            )

    ci_text = CI_WORKFLOW.read_text(encoding="utf-8")
    for marker in (
        "AXEYUM_LEAN_BUDGET_SECS: 0",
        "AXEYUM_LEAN_JOBS: 2",
        "--test lean_crosscheck",
        "lean_crosscheck_representative -- --nocapture --exact",
    ):
        if marker not in ci_text:
            failures.append(
                f"{CI_WORKFLOW.relative_to(ROOT)}: missing representative Lean gate {marker!r}"
            )

    line = "|".join(f"{key}={value}" for key, value in snapshot.items())
    print(f"PARITY_DOCS|{line}")
    if failures:
        for failure in failures:
            print(f"ERROR: {failure}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
