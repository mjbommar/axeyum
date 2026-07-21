#!/usr/bin/env python3
"""Fail when live parity documentation contradicts committed measurements.

This is intentionally a narrow guard, not a natural-language fact checker.  It
owns the claims that have already rotted repeatedly: the generated division
totals, exact dominance-audit denominators, and the paired 20-second p4dfa
control.  New guarded claims should be added only when they have one canonical,
machine-readable artifact.
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

LIVE_DOCS = (
    ROOT / "PLAN.md",
    ROOT / "STATUS.md",
    ROOT / "bench-results" / "SCOREBOARD.md",
    ROOT / "docs" / "plan" / "README.md",
    ROOT / "docs" / "user-guide" / "benchmarks.md",
    GAP_DOC,
)

STALE_PATTERNS = (
    re.compile(r"Z3 (?:still )?decides all 113", re.IGNORECASE),
    re.compile(r"Z3\s+113/113", re.IGNORECASE),
    re.compile(r"p4dfa 113, parity, both hard-capped", re.IGNORECASE),
    re.compile(r"~15/35 rows"),
    re.compile(r"\b19/35 decide-strong\b"),
    re.compile(r"\b23 fragments\b"),
    re.compile(r"\b~73%\b"),
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
            audits.append(audit["summary"])

    axeyum = load_json(AXEYUM_P4DFA)
    z3 = load_json(Z3_P4DFA)
    inventory = load_json(SMTCOMP_INVENTORY)
    qfbv = load_json(SMTCOMP_QFBV)
    provenance = load_json(SMTCOMP_PROVENANCE)
    for artifact in (axeyum, z3):
        config = artifact["config"]
        summary = artifact["summary"]
        if config["timeout_ms"] != 20_000 or summary["files"] != 113:
            raise RuntimeError("p4dfa control is no longer the registered 113-file/20-second cell")
    if axeyum["config"]["corpus_hash"] != z3["config"]["corpus_hash"]:
        raise RuntimeError("p4dfa Axeyum/Z3 controls do not bind the same corpus hash")
    qfbv_division = qfbv["divisions"]["QF_BV"]
    qfbv_solvers = qfbv_division["solvers"]

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
            summary.get("dominant_pct_audited") == 100.0 for summary in audits
        ),
        "dominant_decisions": sum(summary["dominant_candidates"] for summary in audits),
        "audited_decisions": sum(summary["audited_decided"] for summary in audits),
        "lean_checked_unsat": sum(summary["lean_checked_unsat"] for summary in audits),
        "audited_unsat": sum(summary["audited_unsat"] for summary in audits),
        "p4dfa_axeyum_20s": decided(axeyum["summary"]),
        "p4dfa_z3_20s": decided(z3["summary"]),
        "public_inventory_files": inventory["aggregate"]["total"],
        "public_inventory_decided": inventory["aggregate"]["decided_correct"],
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

    required_gap_markers = (
        f"{snapshot['decided']} / {snapshot['files']}",
        f"{snapshot['compared']} oracle-compared",
        f"{snapshot['decide_strong_rows']} / {snapshot['rows']} rows",
        f"{snapshot['fully_dominant_rows']} / {snapshot['complete_audits']} audited rows",
        f"{snapshot['dominant_decisions']} / {snapshot['audited_decisions']} decisions",
        f"{snapshot['lean_checked_unsat']} / {snapshot['audited_unsat']} measured `unsat`",
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
    )
    gap_text = GAP_DOC.read_text(encoding="utf-8")
    for marker in required_gap_markers:
        if marker not in gap_text:
            failures.append(f"{GAP_DOC.relative_to(ROOT)}: missing measured marker {marker!r}")

    line = "|".join(f"{key}={value}" for key, value in snapshot.items())
    print(f"PARITY_DOCS|{line}")
    if failures:
        for failure in failures:
            print(f"ERROR: {failure}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
