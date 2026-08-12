#!/usr/bin/env python3
"""Generate artifacts/claims/DASHBOARD.md from the committed claim ledger.

This is an additive, deterministic aggregator: it reads every
`artifacts/claims/<family>/<id>/claim.json` and emits a single legible markdown
view — what is asserted, how firmly it is believed (`epistemic_status`), which
evidence rows carry it (`kind` + `check_status`), how many concept references
are resolved vs still pending, and the frontier record of every open or
conjectured claim. It fabricates nothing and re-checks nothing: the numbers are
read straight from the committed claim files, whose structure is enforced by
`validate-claims.py` and whose `checked` rows are re-derived by
`check-claim-certificates.py`. Re-running on unchanged claims produces a
byte-identical file (no timestamps, fully sorted).

Usage:
    python3 scripts/gen-claims-dashboard.py

Reads:
    artifacts/claims/*/*/claim.json

Writes:
    artifacts/claims/DASHBOARD.md
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLAIMS = ROOT / "artifacts" / "claims"
OUT_PATH = CLAIMS / "DASHBOARD.md"


def cell(text: str) -> str:
    """Make a string safe inside a markdown table cell (deterministic)."""
    return text.replace("|", "\\|").replace("\n", " ").strip()


def tally(counter: Counter[str]) -> str:
    """`key` n, `key` n — sorted, so the line never reorders between runs."""
    return ", ".join(f"`{k}` {counter[k]}" for k in sorted(counter))


def build_markdown(claims: list[tuple[str, str, dict]]) -> str:
    """claims is a sorted list of (family, id, claim-record) triples."""
    lines: list[str] = []
    lines.append("# Claim Ledger Dashboard")
    lines.append("")
    lines.append(
        "> **Auto-generated. Do not edit by hand.** Regenerate with "
        "`python3 scripts/gen-claims-dashboard.py`."
    )
    lines.append("")
    lines.append(
        "One row per claim under `artifacts/claims/<family>/<id>/claim.json`: "
        "what is asserted, how firmly it is believed, and which evidence rows "
        "carry it. Every value is read straight from a committed claim file — "
        "nothing here is recomputed. The ledger's vocabulary and gates are "
        "described in [`README.md`](README.md) "
        "([ADR-0379](../../docs/research/09-decisions/adr-0379-claim-ledger.md))."
    )
    lines.append("")
    lines.append(
        "`check_status` is per evidence row, not per claim: `checked` means "
        "`scripts/check-claim-certificates.py` re-derives it independently, "
        "`replay-only` means the artifact replays but no certificate exists, "
        "and `not-checked` marks an honest citation or unverified support."
    )
    lines.append("")

    # ------------------------------------------------------------- summary
    statuses: Counter[str] = Counter()
    kinds: Counter[str] = Counter()
    check_statuses: Counter[str] = Counter()
    families: Counter[str] = Counter()
    resolved_refs = 0
    pending_refs = 0
    evidence_rows = 0
    for family, _cid, c in claims:
        families[family] += 1
        statuses[c["epistemic_status"]] += 1
        for ev in c["evidence"]:
            evidence_rows += 1
            kinds[ev["kind"]] += 1
            check_statuses[ev["check_status"]] += 1
        for ref in c["concept_refs"]:
            if ref.get("resolved"):
                resolved_refs += 1
            else:
                pending_refs += 1
    frontier_claims = [t for t in claims if "frontier" in t[2]]

    lines.append("## Summary")
    lines.append("")
    lines.append(
        f"- Claims: {len(claims)} across {len(families)} "
        f"{'family' if len(families) == 1 else 'families'} "
        f"({', '.join(f'`{f}` {families[f]}' for f in sorted(families))})"
    )
    lines.append(f"- Epistemic status: {tally(statuses)}")
    lines.append(f"- Evidence rows: {evidence_rows} — {tally(check_statuses)}")
    lines.append(f"- Evidence kinds: {tally(kinds)}")
    lines.append(
        f"- Concept references: {resolved_refs + pending_refs} — "
        f"{resolved_refs} resolved, {pending_refs} pending"
    )
    lines.append(
        f"- Frontier records (open/conjectured claims): {len(frontier_claims)}"
    )
    lines.append("")

    # -------------------------------------------------------------- claims
    lines.append("## Claims")
    lines.append("")
    for family in sorted(families):
        lines.append(f"### `{family}`")
        lines.append("")
        lines.append(
            "| Claim | Title | Status | Evidence (kind: check_status) "
            "| Refs resolved | Refs pending |"
        )
        lines.append("| --- | --- | --- | --- | ---: | ---: |")
        for fam, cid, c in claims:
            if fam != family:
                continue
            evidence = "<br>".join(
                f"`{ev['kind']}`: {ev['check_status']}" for ev in c["evidence"]
            ) or "—"
            resolved = sum(1 for r in c["concept_refs"] if r.get("resolved"))
            pending = sum(1 for r in c["concept_refs"] if not r.get("resolved"))
            lines.append(
                f"| [`{cid}`]({family}/{cid}/claim.json) "
                f"| {cell(c['title'])} "
                f"| `{c['epistemic_status']}` "
                f"| {evidence} | {resolved} | {pending} |"
            )
        lines.append("")

    # ------------------------------------------------------------ frontier
    lines.append("## Frontier")
    lines.append("")
    if not frontier_claims:
        lines.append(
            "No open or conjectured claims in the ledger — every claim carries "
            "a settled status."
        )
        lines.append("")
    else:
        lines.append(
            "Open and conjectured claims carry a mandatory `frontier` record: "
            "what is currently known, and the concrete artifact that would "
            "settle the claim. These are the ledger's work items."
        )
        lines.append("")
        for family, cid, c in frontier_claims:
            fr = c["frontier"]
            lines.append(f"### `{cid}` — {c['title'].strip()}")
            lines.append("")
            lines.append(f"- Status: `{c['epistemic_status']}`")
            lines.append(f"- Claim: [`{family}/{cid}/claim.json`]({family}/{cid}/claim.json)")
            lines.append("")
            lines.append("**Known**")
            lines.append("")
            for known in fr["known"]:
                lines.append(f"- {known.strip()}")
            lines.append("")
            lines.append(f"**Would settle:** {fr['would_settle'].strip()}")
            lines.append("")
            if "attack_notes" in fr:
                lines.append(f"**Attack notes:** {fr['attack_notes'].strip()}")
                lines.append("")

    # ---------------------------------------------------------- provenance
    lines.append("## Provenance")
    lines.append("")
    lines.append(
        "Generated by [`scripts/gen-claims-dashboard.py`](../../scripts/gen-claims-dashboard.py) "
        "from the following committed claim files (deterministic — no "
        "timestamps, fully sorted; re-running on unchanged claims yields a "
        "byte-identical file):"
    )
    lines.append("")
    for family, cid, _c in claims:
        lines.append(f"- `artifacts/claims/{family}/{cid}/claim.json`")
    lines.append("")
    lines.append("Regenerate with `python3 scripts/gen-claims-dashboard.py`.")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    claim_files = sorted(CLAIMS.glob("*/*/claim.json"))
    if not claim_files:
        print("no claims found under artifacts/claims/*/*/claim.json")
        return 1
    claims = [
        (path.parent.parent.name, path.parent.name, json.loads(path.read_text()))
        for path in claim_files
    ]
    OUT_PATH.write_text(build_markdown(claims))
    print(
        f"wrote {OUT_PATH.relative_to(ROOT)}: {len(claims)} claims, "
        f"{sum(len(c['evidence']) for _f, _i, c in claims)} evidence rows"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
