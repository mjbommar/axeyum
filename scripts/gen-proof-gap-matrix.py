#!/usr/bin/env python3
"""Generate the proof-gap matrix from committed dominance audits.

The dominance summaries historically collapse several different stages into
one UNSAT denominator.  This generator keeps the per-instance pipeline
explicit:

    baseline UNSAT -> evidence-audit UNSAT -> certified -> checker accepted
      -> trust-hole free -> Lean reconstructed

It writes deterministic JSON and Markdown under docs/plan/generated.  Use
``--check`` in CI to fail when committed outputs are stale.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
AUDIT_DIR = ROOT / "bench-results" / "dominance"
OUT_DIR = ROOT / "docs" / "plan" / "generated"
OUT_JSON = OUT_DIR / "proof-gap-matrix.json"
OUT_MD = OUT_DIR / "proof-gap-matrix.md"

CATEGORY_ORDER = (
    "proof-production-error",
    "uncertified-and-unchecked",
    "uncertified-but-checked",
    "evidence-check-gap",
    "trust-hole-and-lean-gap",
    "trust-hole",
    "lean-reconstruction-gap",
    "dominant",
)

CATEGORY_DESCRIPTIONS = {
    "proof-production-error": "Evidence production did not reproduce UNSAT.",
    "uncertified-and-unchecked": "The UNSAT route is neither certified nor independently checked.",
    "uncertified-but-checked": "Reserved invalid combination; normalized into uncertified-and-unchecked.",
    "evidence-check-gap": "Certified evidence exists but did not pass its independent checker.",
    "trust-hole-and-lean-gap": "Checked evidence retains a trust hole and has no Lean reconstruction.",
    "trust-hole": "Lean reconstruction exists, but a declared trust hole remains.",
    "lean-reconstruction-gap": "Certified, checked, trust-free evidence lacks Lean reconstruction.",
    "dominant": "Certified, checked, trust-free, and Lean-reconstructed UNSAT.",
}


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def load_audits() -> list[dict]:
    audits = []
    for path in sorted(AUDIT_DIR.glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        if not data.get("complete_audit"):
            continue
        data["_source"] = rel(path)
        data["_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
        audits.append(data)
    if not audits:
        raise RuntimeError(f"no complete dominance audits under {AUDIT_DIR}")
    return audits


def proof_category(instance: dict) -> str:
    if instance.get("audit_outcome") != "unsat":
        return "proof-production-error"
    certified = instance.get("evidence_certified") is True
    # Historical audit artifacts called `Evidence::check` even for
    # `Unsat(None)`, whose no-certificate behavior is structural `Ok(true)`.
    # A real independent check requires a certified artifact first.
    checked = certified and instance.get("evidence_checked") is True
    lean = instance.get("lean_checked") is True
    holes = bool(instance.get("trust_holes"))
    if not certified and not checked:
        return "uncertified-and-unchecked"
    if not certified:
        return "uncertified-but-checked"
    if not checked:
        return "evidence-check-gap"
    if holes and not lean:
        return "trust-hole-and-lean-gap"
    if holes:
        return "trust-hole"
    if not lean:
        return "lean-reconstruction-gap"
    return "dominant"


def stage_counts(instances: list[dict]) -> dict[str, int]:
    return {
        "baseline_unsat": len(instances),
        "audit_unsat": sum(i.get("audit_outcome") == "unsat" for i in instances),
        "evidence_certified": sum(
            i.get("evidence_certified") is True for i in instances
        ),
        "audit_reported_checked": sum(
            i.get("evidence_checked") is True for i in instances
        ),
        "evidence_checked": sum(
            i.get("evidence_certified") is True
            and i.get("evidence_checked") is True
            for i in instances
        ),
        "trust_hole_free": sum(
            i.get("audit_outcome") == "unsat" and not i.get("trust_holes")
            for i in instances
        ),
        "lean_checked": sum(i.get("lean_checked") is True for i in instances),
        "dominant_unsat": sum(proof_category(i) == "dominant" for i in instances),
    }


def aggregate_group(instances: list[dict]) -> dict[str, int]:
    counts = stage_counts(instances)
    counts["trust_hole_instances"] = sum(bool(i.get("trust_holes")) for i in instances)
    counts["proof_errors"] = sum(
        i.get("audit_outcome") != "unsat" for i in instances
    )
    return counts


def build_report(audits: list[dict]) -> dict:
    all_instances = []
    rows = []
    for audit in audits:
        instances = [
            i for i in audit.get("instances", []) if i.get("baseline_outcome") == "unsat"
        ]
        all_instances.extend(instances)
        counts = aggregate_group(instances)
        blockers = Counter(proof_category(i) for i in instances)
        blockers.pop("dominant", None)
        rows.append(
            {
                "logic": audit.get("logic") or "unknown",
                "slice": audit.get("slice") or audit.get("baseline") or "unknown",
                "source": audit["_source"],
                **counts,
                "blockers": dict(
                    sorted(blockers.items(), key=lambda item: (-item[1], item[0]))
                ),
            }
        )

    categories = Counter(proof_category(i) for i in all_instances)
    evidence_groups: dict[str, list[dict]] = {}
    for instance in all_instances:
        kind = instance.get("evidence_kind") or "(none)"
        evidence_groups.setdefault(kind, []).append(instance)
    evidence_kinds = [
        {"evidence_kind": kind, **aggregate_group(instances)}
        for kind, instances in evidence_groups.items()
    ]
    evidence_kinds.sort(
        key=lambda row: (
            -(row["baseline_unsat"] - row["dominant_unsat"]),
            -row["baseline_unsat"],
            row["evidence_kind"],
        )
    )

    trust_holes = Counter(
        hole for instance in all_instances for hole in instance.get("trust_holes", [])
    )
    proof_errors = []
    for audit in audits:
        for instance in audit.get("instances", []):
            if (
                instance.get("baseline_outcome") == "unsat"
                and instance.get("audit_outcome") != "unsat"
            ):
                proof_errors.append(
                    {
                        "logic": audit.get("logic") or "unknown",
                        "file": instance.get("file") or "unknown",
                        "phase": instance.get("audit_phase") or "unknown",
                        "error": instance.get("error") or "unknown",
                    }
                )
    proof_errors.sort(key=lambda row: (row["logic"], row["file"]))
    rows.sort(key=lambda row: (row["logic"], row["slice"], row["source"]))

    return {
        "version": 1,
        "summary": {
            "complete_audits": len(audits),
            **aggregate_group(all_instances),
        },
        "categories": [
            {
                "category": category,
                "instances": categories.get(category, 0),
                "description": CATEGORY_DESCRIPTIONS[category],
            }
            for category in CATEGORY_ORDER
        ],
        "evidence_kinds": evidence_kinds,
        "trust_holes": [
            {"trust_hole": hole, "instances": count}
            for hole, count in sorted(trust_holes.items(), key=lambda item: (-item[1], item[0]))
        ],
        "proof_errors": proof_errors,
        "rows": rows,
        "sources": [
            {"path": audit["_source"], "sha256": audit["_sha256"]}
            for audit in audits
        ],
    }


def pct(numerator: int, denominator: int) -> str:
    if denominator == 0:
        return "-"
    return f"{100.0 * numerator / denominator:.1f}%"


def markdown(report: dict) -> str:
    summary = report["summary"]
    lines = [
        "# Generated proof-gap matrix",
        "",
        "> Generated by `scripts/gen-proof-gap-matrix.py` from the committed",
        "> `bench-results/dominance/*.json` artifacts. Do not hand-edit.",
        "",
        "This matrix separates solver outcomes from evidence production, independent",
        "checking, declared trust, and Lean reconstruction. Counts cover baseline UNSAT",
        "instances only; SAT model replay is outside this report.",
        "",
        "## Pipeline snapshot",
        "",
        "| Stage | Instances | Retained from baseline UNSAT |",
        "|---|---:|---:|",
    ]
    stages = (
        ("Baseline UNSAT", "baseline_unsat"),
        ("Evidence audit reproduced UNSAT", "audit_unsat"),
        ("Evidence marked certified", "evidence_certified"),
        ("Evidence independently checked", "evidence_checked"),
        ("Audit UNSAT with no declared trust hole", "trust_hole_free"),
        ("Lean reconstruction checked", "lean_checked"),
        ("All dominance conditions", "dominant_unsat"),
    )
    for label, key in stages:
        value = summary[key]
        lines.append(f"| {label} | {value} | {pct(value, summary['baseline_unsat'])} |")

    lines.extend(
        [
            "",
            "The stages are not a monotone funnel: one `bare-unsat` row has an",
            "independent Lean reconstruction but remains uncertified, and one",
            "Lean-checked DRAT row retains a declared",
            "`bit-blast` trust hole. The final row is therefore the conjunction, not the",
            "minimum of the preceding totals. Historical audit JSON reports",
            f"`evidence_checked=true` for {summary['audit_reported_checked'] - summary['evidence_checked']} uncertified `bare-unsat` rows because the",
            "no-certificate",
            "`Evidence::check` path returns structural `Ok(true)`; this generator",
            "normalizes those rows to independently unchecked.",
            "",
            "## Exclusive outcome categories",
            "",
            "| Category | Instances | Meaning |",
            "|---|---:|---|",
        ]
    )
    for row in report["categories"]:
        lines.append(
            f"| `{row['category']}` | {row['instances']} | {row['description']} |"
        )

    lines.extend(
        [
            "",
            "## Evidence-kind gaps",
            "",
            "Sorted by non-dominant count, then population. This names the repeated",
            "mechanisms that should drive reconstruction work.",
            "",
            "| Evidence kind | Baseline UNSAT | Certified | Checked | Lean | Trust holes | Dominant | Gap |",
            "|---|---:|---:|---:|---:|---:|---:|---:|",
        ]
    )
    for row in report["evidence_kinds"]:
        gap = row["baseline_unsat"] - row["dominant_unsat"]
        lines.append(
            f"| `{row['evidence_kind']}` | {row['baseline_unsat']} | "
            f"{row['evidence_certified']} | {row['evidence_checked']} | "
            f"{row['lean_checked']} | {row['trust_hole_instances']} | "
            f"{row['dominant_unsat']} | {gap} |"
        )

    lines.extend(
        [
            "",
            "## Per-row matrix",
            "",
            "| Logic | Slice | Baseline UNSAT | Audit UNSAT | Certified | Checked | Lean | Trust holes | Dominant | Proof errors | Leading blockers |",
            "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---|",
        ]
    )
    for row in report["rows"]:
        blockers = ", ".join(f"`{key}`={value}" for key, value in row["blockers"].items()) or "-"
        lines.append(
            f"| {row['logic']} | `{row['slice']}` | {row['baseline_unsat']} | "
            f"{row['audit_unsat']} | {row['evidence_certified']} | "
            f"{row['evidence_checked']} | {row['lean_checked']} | "
            f"{row['trust_hole_instances']} | {row['dominant_unsat']} | "
            f"{row['proof_errors']} | {blockers} |"
        )

    lines.extend(["", "## Declared trust holes", ""])
    if report["trust_holes"]:
        lines.extend(["| Trust hole | Instances |", "|---|---:|"])
        for row in report["trust_holes"]:
            lines.append(f"| `{row['trust_hole']}` | {row['instances']} |")
    else:
        lines.append("None.")

    lines.extend(["", "## Proof-production errors", ""])
    if report["proof_errors"]:
        lines.extend(["| Logic | File | Phase | Error |", "|---|---|---|---|"])
        for row in report["proof_errors"]:
            error = row["error"].replace("|", "\\|")
            lines.append(
                f"| {row['logic']} | `{row['file']}` | `{row['phase']}` | {error} |"
            )
    else:
        lines.append("None.")

    categories = {row["category"]: row["instances"] for row in report["categories"]}
    lines.extend(
        [
            "",
            "## Evidence-driven priority",
            "",
            f"1. Replace the {categories['uncertified-and-unchecked'] + categories['uncertified-but-checked']} uncertified audit-row occurrences with serialized, certified evidence and independently check every route. Use the [deduplicated shape census](proof-gap-shape-census.md) for mechanism prevalence.",
            f"2. Add Lean reconstruction for the {categories['lean-reconstruction-gap']} already certified, checked, trust-free instances.",
            f"3. Eliminate the {categories['trust-hole-and-lean-gap'] + categories['trust-hole']} declared trust-hole instances rather than counting Lean module acceptance alone.",
            f"4. Fix the {categories['proof-production-error']} proof-production errors and rerun their exact committed rows.",
            "",
            "These priorities are prevalence-ranked within the committed audits. They do",
            "not authorize a mechanism until an exact residual-shape census identifies a",
            "shared implementation boundary.",
            "",
        ]
    )
    return "\n".join(lines)


def render_json(report: dict) -> str:
    return json.dumps(report, indent=2, sort_keys=True) + "\n"


def write_or_check(path: Path, content: str, check: bool) -> bool:
    if check:
        actual = path.read_text(encoding="utf-8") if path.exists() else None
        if actual != content:
            print(f"stale generated artifact: {rel(path)}")
            return False
        return True
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return True


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check", action="store_true", help="fail if committed outputs are stale"
    )
    args = parser.parse_args()

    report = build_report(load_audits())
    ok_json = write_or_check(OUT_JSON, render_json(report), args.check)
    ok_md = write_or_check(OUT_MD, markdown(report), args.check)
    summary = report["summary"]
    print(
        "PROOF_GAPS|"
        f"audits={summary['complete_audits']}|"
        f"baseline_unsat={summary['baseline_unsat']}|"
        f"audit_unsat={summary['audit_unsat']}|"
        f"lean_checked={summary['lean_checked']}|"
        f"dominant_unsat={summary['dominant_unsat']}|"
        f"trust_holes={summary['trust_hole_instances']}|"
        f"proof_errors={summary['proof_errors']}"
    )
    return 0 if ok_json and ok_md else 1


if __name__ == "__main__":
    raise SystemExit(main())
