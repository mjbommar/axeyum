#!/usr/bin/env python3
"""Produce the golden fixture's run record from REAL ledger artifacts.

WHY THIS EXISTS. The golden tests need a run record, and a hand-written one
would be synthetic evidence -- the exact thing this strand forbids. So this
script performs a real check over real files and records what it found.

WHAT IT CHECKS (and what it therefore may claim):
  * each fixture fact validates against `artifacts/ontology/fact.schema.json`;
  * each records `epistemic_status: proved` with a `proof_route`;
  * each carries at least one evidence row whose `check_status` is `checked`;
  * neither claims `axiom_footprint: []` on a route that cannot deliver
    axiom-freedom (only `kernel-lean` can) -- the fact schema's own rule.

NOTE THE SCOPE. These are claims about the LEDGER'S RECORD of two facts, not
about the mathematics. This script did not check that Boolean conjunction is
commutative and does not say it did; the fact's own status axes are pulled from
the ledger by a `statement` block, which is a different thing and is the point of
the architecture.

THE EXIT STATUS DEPENDS ON THE FINDING, not on completion: any failed check
means exit 1 and the record is still written, carrying `exit_status: 1` and
`outcome: refuted`, so a consumer sees red evidence rather than a missing file.

Usage:  python3 render/tests/fixtures/make_run_record.py [--repo-root DIR]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

FIXTURE_FACTS = ["F:bool-and-comm", "F:excluded-middle"]
SCHEMA_REL = "artifacts/ontology/fact.schema.json"
SVG_NAME = "fixture-footprints.svg"
SVG_REL = "render/tests/fixtures/" + SVG_NAME
# Only this route's `axiom_footprint: []` means axiom-freedom; see the
# `proof_route` description in fact.schema.json.
AXIOM_FREE_ROUTE = "kernel-lean"


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fact_path(root: Path, fact_id: str) -> Path:
    return root / "artifacts" / "facts" / (fact_id.replace(":", "-", 1) + ".json")


def commit_epoch(root: Path) -> dict:
    """The pinned commit and its committer time. No wall clock anywhere."""
    out = subprocess.run(
        ["git", "log", "-1", "--format=%H %ct"],
        cwd=root,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.split()
    return {"unix": int(out[1]), "source": "commit", "commit": out[0]}


def render_svg(rows: list[list]) -> str:
    """A minimal bar chart of the measured counts. Deterministic and ASCII."""
    bar_h, gap, left, top, unit = 18, 10, 190, 34, 26
    height = top + len(rows) * 2 * (bar_h + gap) + 24
    width = 520
    out = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}" role="img" '
        f'aria-label="axiom footprint and evidence rows per fixture fact">',
        '<title>Axiom footprint and evidence rows per fixture fact</title>',
        f'<text x="8" y="20" font-family="monospace" font-size="13">'
        f'axiom footprint (dark) and evidence rows (light), per fact</text>',
    ]
    y = top
    for fact, _status, _ext, route, footprint, evidence, _checked, _checkers in rows:
        for label, value, fill in (
            (f"{fact} footprint", footprint or 0, "#333333"),
            (f"{route} evidence", evidence, "#999999"),
        ):
            out.append(
                f'<text x="8" y="{y + 13}" font-family="monospace" font-size="11">{label}</text>'
            )
            out.append(
                f'<rect x="{left}" y="{y}" width="{max(value * unit, 1)}" height="{bar_h}" '
                f'fill="{fill}" />'
            )
            out.append(
                f'<text x="{left + max(value * unit, 1) + 6}" y="{y + 13}" '
                f'font-family="monospace" font-size="11">{value}</text>'
            )
            y += bar_h + gap
    out.append("</svg>")
    return "\n".join(out) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo-root", default=None)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    here = Path(__file__).resolve().parent
    root = Path(args.repo_root).resolve() if args.repo_root else here.parents[2]
    out_path = Path(args.out) if args.out else here / "run-fact-ledger-check.json"

    schema_path = root / SCHEMA_REL
    schema = json.loads(schema_path.read_text())
    try:
        import jsonschema

        validator = jsonschema.Draft202012Validator(schema)
    except ImportError:  # pragma: no cover - environment without jsonschema
        print("make_run_record: jsonschema is required to produce this record", file=sys.stderr)
        return 2

    findings: list[str] = []
    rows: list[list] = []
    claims: list[dict] = []
    inputs = [{"path": SCHEMA_REL, "sha256": sha256_file(schema_path), "role": "schema"}]

    for fact_id in FIXTURE_FACTS:
        path = fact_path(root, fact_id)
        rel = str(path.relative_to(root))
        fact = json.loads(path.read_text())
        inputs.append({"path": rel, "sha256": sha256_file(path), "role": "fact"})

        errors = sorted(validator.iter_errors(fact), key=lambda e: list(e.path))
        for err in errors:
            findings.append(f"{fact_id}: schema violation at {list(err.path)}: {err.message}")

        status = fact.get("epistemic_status")
        route = fact.get("proof_route")
        footprint = fact.get("axiom_footprint")
        evidence = fact.get("evidence", [])
        checked = [e for e in evidence if e.get("check_status") == "checked"]
        checkers = sorted({c for e in evidence for c in e.get("checkers", [])})

        if status != "proved":
            findings.append(f"{fact_id}: epistemic_status is {status!r}, expected 'proved'")
        if not route:
            findings.append(f"{fact_id}: no proof_route recorded")
        if footprint is None:
            findings.append(f"{fact_id}: proved without an axiom_footprint")
        if not checked:
            findings.append(f"{fact_id}: no evidence row with check_status 'checked'")
        if footprint == [] and route != AXIOM_FREE_ROUTE:
            findings.append(
                f"{fact_id}: empty axiom_footprint on route {route!r}, which cannot "
                "deliver axiom-freedom"
            )

        rows.append(
            [
                fact_id,
                status,
                fact.get("external_status") or "not recorded",
                route or "none",
                len(footprint) if footprint is not None else None,
                len(evidence),
                len(checked),
                len(checkers),
            ]
        )
        claims.append(
            {
                "key": fact_id.replace(":", "-", 1).lower(),
                "status": "checked",
                "statement": (
                    f"The ledger entry {fact_id} validates against {SCHEMA_REL} and records "
                    f"epistemic_status={status} on proof_route={route} with an axiom footprint of "
                    f"{len(footprint) if footprint is not None else 0} entr"
                    f"{'y' if footprint is not None and len(footprint) == 1 else 'ies'} and "
                    f"{len(evidence)} evidence row(s), {len(checked)} of them check_status=checked, "
                    f"naming {len(checkers)} distinct checker(s)."
                ),
                "supports": {"kind": "fact", "id": fact_id},
            }
        )

    claims.append(
        {
            "key": "no-unearned-axiom-freedom",
            "status": "checked",
            "statement": (
                "Neither fixture fact records an empty axiom_footprint on a route other than "
                "kernel-lean, so neither claims an axiom-freedom its route cannot deliver."
            ),
        }
    )

    # The figure is DRAWN FROM THE ROWS ABOVE, not transcribed: a changed
    # footprint changes the picture. It is plain ASCII SVG with no external
    # reference, so it satisfies the HTML self-containment lint too.
    # The path RECORDED is always the canonical one; the file is written next to
    # whatever `--out` names, so a check that regenerates the record into a
    # temporary directory does not write into the shared checkout. (A gate with
    # side effects on the tree it is checking is how this repository once got a
    # DIRTY WORKTREE stamp fired by the harness's own output.)
    svg_path = out_path.parent / SVG_NAME
    svg_path.write_text(render_svg(rows))

    ok = not findings
    exit_status = 0 if ok else 1
    record = {
        "schema_version": 1,
        "id": "R:fixture-fact-ledger-check",
        "provenance": {
            "generator": "render/tests/fixtures/make_run_record.py",
            "command": "python3 render/tests/fixtures/make_run_record.py",
            "inputs": inputs,
            "exit_status": exit_status,
            "epoch": commit_epoch(root),
        },
        "summary": (
            f"Validated {len(FIXTURE_FACTS)} fact-ledger entries against {SCHEMA_REL} and "
            f"checked their recorded status, route, footprint and evidence rows: "
            f"{len(findings)} finding(s)."
        ),
        "outcome": "established" if ok else "refuted",
        "claims": claims,
        "stats": {
            "facts_checked": len(FIXTURE_FACTS),
            "findings": len(findings),
            "evidence_rows": sum(r[5] for r in rows),
            "checked_evidence_rows": sum(r[6] for r in rows),
        },
        "tables": {
            "fixture-facts": {
                "columns": [
                    "fact",
                    "established here",
                    "externally",
                    "proof route",
                    "axiom footprint",
                    "evidence rows",
                    "checked rows",
                    "distinct checkers",
                ],
                "rows": rows,
            }
        },
        "artifacts": [
            {
                "path": SVG_REL,
                "sha256": sha256_file(svg_path),
                "label": "axiom-footprint and evidence-row counts, drawn from the rows above",
                "bytes": svg_path.stat().st_size,
                "media_type": "image/svg+xml",
            }
        ],
        "replay": {
            "line": "python3 render/tests/fixtures/make_run_record.py --out /dev/stdout",
            "cwd": ".",
            "expected_exit_status": 0,
            "expected_seconds": 1,
        },
        "notes": (
            "Scope: this run checked the LEDGER'S RECORD of two facts. It did not check the "
            "mathematics, and no claim here says it did."
        ),
    }
    if findings:
        record["notes"] += " Findings: " + "; ".join(findings)

    out_path.write_text(json.dumps(record, indent=2, sort_keys=True, ensure_ascii=True) + "\n")
    for f in findings:
        print(f"FINDING: {f}", file=sys.stderr)
    print(f"wrote {out_path} (exit_status {exit_status})", file=sys.stderr)
    return exit_status


if __name__ == "__main__":
    sys.exit(main())
