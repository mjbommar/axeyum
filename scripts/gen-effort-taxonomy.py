#!/usr/bin/env python3
"""Generate the D0 effort-taxonomy distribution + report from episodes.json.

L3-D0 (docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md) asks
where theorem effort actually goes, classified into a stable taxonomy, so the
D1-D4 phase order can be chosen from a measurement rather than an assumption.

This script is the GENERATOR half: it reads the hand-curated
artifacts/effort-taxonomy/{taxonomy,episodes}.json and computes the derived
distribution.json + report.md deterministically. It does not decide whether
the inputs are *valid* -- that is scripts/check-effort-taxonomy.py's job,
which imports compute_distribution() from here rather than reimplementing it
(this is a data-consistency checker, not a soundness-critical certificate
validator, so one implementation is the right amount of machinery -- see
CLAUDE.md's "two independent readers" rule, which is for cases where a wrong
answer would ship as a trusted mathematical result).

Usage:
    python3 scripts/gen-effort-taxonomy.py            # regenerate in place
    python3 scripts/gen-effort-taxonomy.py --check     # exit 1 if stale
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_DIR = ROOT / "artifacts" / "effort-taxonomy"
TAXONOMY_PATH = ARTIFACT_DIR / "taxonomy.json"
EPISODES_PATH = ARTIFACT_DIR / "episodes.json"
DISTRIBUTION_PATH = ARTIFACT_DIR / "distribution.json"
REPORT_PATH = ARTIFACT_DIR / "report.md"


def load_inputs(
    taxonomy_path: Path = TAXONOMY_PATH, episodes_path: Path = EPISODES_PATH
) -> tuple[dict, list[dict]]:
    taxonomy = json.loads(taxonomy_path.read_text())
    episodes = json.loads(episodes_path.read_text())
    return taxonomy, episodes


def compute_distribution(taxonomy: dict, episodes: list[dict]) -> dict:
    """Pure function: episodes + taxonomy -> the derived counts.

    Kept side-effect-free and imported directly by the checker so the
    generator and the checker can never silently diverge in what they mean
    by "the distribution".
    """
    cat_order = taxonomy["category_order"]
    primary_counts: dict[str, int] = {c: 0 for c in cat_order}
    secondary_counts: dict[str, int] = {c: 0 for c in cat_order}
    kind_counts: dict[str, int] = {}
    domain_counts: dict[str, int] = {}
    basis_counts: dict[str, int] = {}
    cat_by_domain: dict[str, dict[str, int]] = {c: {} for c in cat_order}

    for ep in episodes:
        pc = ep["primary_category"]
        primary_counts[pc] = primary_counts.get(pc, 0) + 1
        for sc in ep.get("secondary_categories", []):
            secondary_counts[sc] = secondary_counts.get(sc, 0) + 1
        kind_counts[ep["kind"]] = kind_counts.get(ep["kind"], 0) + 1
        domain_counts[ep["domain"]] = domain_counts.get(ep["domain"], 0) + 1
        basis_counts[ep["basis"]] = basis_counts.get(ep["basis"], 0) + 1
        cat_by_domain.setdefault(pc, {})
        cat_by_domain[pc][ep["domain"]] = cat_by_domain[pc].get(ep["domain"], 0) + 1

    total = len(episodes)

    # A grouping the report leans on: which primary categories are the ones
    # the D0 spec actually named, vs the one this measurement added.
    spec_categories = [
        c for c in cat_order if c != "infrastructure_maintenance"
    ]
    spec_total = sum(primary_counts[c] for c in spec_categories)
    added_total = primary_counts.get("infrastructure_maintenance", 0)

    # The "trust + plumbing" share: safety_evidence + integration +
    # infrastructure_maintenance, none of which is proof search or the
    # missing-definitions/retrieval work D1-D4 targets.
    trust_and_plumbing = (
        primary_counts.get("safety_evidence", 0)
        + primary_counts.get("integration", 0)
        + primary_counts.get("infrastructure_maintenance", 0)
    )
    # The share the D1-D4 roadmap is explicitly aimed at:
    # missing_definitions (D1), retrieval (D2), semantic_falsification (D3),
    # proof_assembly (the thing D4/D5 exist to make cheaper).
    roadmap_targeted = (
        primary_counts.get("missing_definitions", 0)
        + primary_counts.get("retrieval", 0)
        + primary_counts.get("semantic_falsification", 0)
        + primary_counts.get("proof_assembly", 0)
    )

    return {
        "total_episodes": total,
        "floor": taxonomy["floor"],
        "primary_category_counts": primary_counts,
        "secondary_category_counts": secondary_counts,
        "kind_counts": kind_counts,
        "domain_counts": domain_counts,
        "basis_counts": basis_counts,
        "primary_category_by_domain": cat_by_domain,
        "spec_named_categories_total": spec_total,
        "added_category_total": added_total,
        "trust_and_plumbing_total": trust_and_plumbing,
        "roadmap_targeted_total": roadmap_targeted,
    }


def render_report(taxonomy: dict, episodes: list[dict], dist: dict) -> str:
    lines: list[str] = []
    lines.append("# D0 effort taxonomy -- generated report")
    lines.append("")
    lines.append(
        "Generated by `scripts/gen-effort-taxonomy.py` from "
        "`artifacts/effort-taxonomy/{taxonomy,episodes}.json`. Do not hand-edit; "
        "edit the JSON and regenerate."
    )
    lines.append("")
    lines.append(
        f"**{dist['total_episodes']} episodes** classified "
        f"(floor: {dist['floor']})."
    )
    lines.append("")
    lines.append("## Primary category distribution")
    lines.append("")
    lines.append("| category | count | share |")
    lines.append("| --- | ---: | ---: |")
    total = dist["total_episodes"]
    for cat in taxonomy["category_order"]:
        n = dist["primary_category_counts"].get(cat, 0)
        share = f"{100.0 * n / total:.0f}%" if total else "0%"
        lines.append(f"| `{cat}` | {n} | {share} |")
    lines.append("")
    lines.append(
        f"Categories the D0 spec named directly account for "
        f"{dist['spec_named_categories_total']}/{total}; "
        f"`infrastructure_maintenance` (added, see taxonomy.json's "
        f"`category_additions`) accounts for {dist['added_category_total']}/{total}."
    )
    lines.append("")
    lines.append(
        f"Trust-and-plumbing share (`safety_evidence` + `integration` + "
        f"`infrastructure_maintenance`): "
        f"{dist['trust_and_plumbing_total']}/{total}. Roadmap-targeted share "
        f"(`missing_definitions` + `retrieval` + `semantic_falsification` + "
        f"`proof_assembly`): {dist['roadmap_targeted_total']}/{total}."
    )
    lines.append("")
    lines.append("## Kind (completed / partial / declined)")
    lines.append("")
    for k in sorted(dist["kind_counts"]):
        lines.append(f"- `{k}`: {dist['kind_counts'][k]}")
    lines.append("")
    lines.append("## Domain (mathematical / infrastructural)")
    lines.append("")
    for d in sorted(dist["domain_counts"]):
        lines.append(f"- `{d}`: {dist['domain_counts'][d]}")
    lines.append("")
    lines.append("## Classification basis")
    lines.append("")
    for b in sorted(dist["basis_counts"]):
        lines.append(f"- `{b}`: {dist['basis_counts'][b]}")
    self_report_ids = sorted(
        ep["id"] for ep in episodes if ep["basis"] == "self-report"
    )
    lines.append("")
    lines.append(
        "Episodes resting on self-report alone (no independently-checked "
        "commit/ADR/file citation): " + ", ".join(f"`{i}`" for i in self_report_ids)
    )
    lines.append("")
    lines.append(
        "`corroborated` means an independently-checked artifact (a commit "
        "that resolves in this repository's object store, an ADR file that "
        "exists, or a source file that exists) confirms the episode's claimed "
        "output is real. It does NOT independently confirm the taxonomy "
        "LABEL is right -- that judgment is always drawn from the episode's "
        "own self-reported narrative."
    )
    lines.append("")
    return "\n".join(lines) + "\n"


def write_outputs(taxonomy: dict, episodes: list[dict]) -> tuple[str, str]:
    dist = compute_distribution(taxonomy, episodes)
    dist_json = json.dumps(dist, indent=2, sort_keys=True) + "\n"
    report_md = render_report(taxonomy, episodes, dist)
    return dist_json, report_md


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="exit 1 if distribution.json/report.md are stale relative to the JSON inputs",
    )
    args = parser.parse_args()

    taxonomy, episodes = load_inputs()
    dist_json, report_md = write_outputs(taxonomy, episodes)

    if args.check:
        stale = []
        if not DISTRIBUTION_PATH.exists() or DISTRIBUTION_PATH.read_text() != dist_json:
            stale.append(str(DISTRIBUTION_PATH))
        if not REPORT_PATH.exists() or REPORT_PATH.read_text() != report_md:
            stale.append(str(REPORT_PATH))
        if stale:
            print("STALE: " + ", ".join(stale) + " -- run without --check to regenerate")
            return 1
        print("EFFORT_TAXONOMY_GEN|status=fresh")
        return 0

    DISTRIBUTION_PATH.write_text(dist_json)
    REPORT_PATH.write_text(report_md)
    print(f"EFFORT_TAXONOMY_GEN|episodes={len(episodes)}|wrote={DISTRIBUTION_PATH.name},{REPORT_PATH.name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
