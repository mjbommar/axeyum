#!/usr/bin/env python3
"""Render `docs/plan/generated/carrier-correspondence.md` from the ledger.

Source: `artifacts/carrier-correspondence/carrier-correspondence-v1.json`.
Regenerate with `python3 scripts/gen-carrier-correspondence-md.py`; `--check`
is the drift gate (registered beside `check-carrier-correspondence.py` in
`scripts/check.sh` and the `justfile`).
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "artifacts" / "carrier-correspondence" / "carrier-correspondence-v1.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "carrier-correspondence.md"

GRADE_ORDER = [
    "same-statement",
    "constructively-stronger",
    "constructively-weaker",
    "different-object",
    "no-counterpart",
]

GRADE_LABEL = {
    "same-statement": "Same statement",
    "constructively-stronger": "Constructively stronger (ours)",
    "constructively-weaker": "Constructively weaker (ours)",
    "different-object": "Different object",
    "no-counterpart": "No counterpart",
}


def relative(path: Path) -> str:
    return str(path.relative_to(ROOT))


def load(path: Path) -> Any:
    with path.open(encoding="utf-8") as fh:
        return json.load(fh)


def md_escape(text: str) -> str:
    return text.replace("|", "\\|").replace("\n", " ")


def render(doc: dict[str, Any]) -> str:
    rows: list[dict[str, Any]] = doc.get("rows", [])
    counts = {g: 0 for g in GRADE_ORDER}
    for row in rows:
        g = row.get("grade")
        if g in counts:
            counts[g] += 1

    lines: list[str] = []
    lines.append("# Carrier correspondence ledger")
    lines.append("")
    lines.append(
        "> **Generated; do not edit by hand.** Source: "
        f"[`{relative(LEDGER)}`](../../../{relative(LEDGER)}). Regenerate with "
        "`python3 scripts/gen-carrier-correspondence-md.py`; `--check` is the "
        "drift gate, registered in `scripts/check.sh` and the `justfile` beside "
        "`check-carrier-correspondence.py --check`."
    )
    lines.append("")
    lines.append(
        "One row per (Axeyum carrier, Mathlib counterpart) pair "
        "(`docs/math-department/14-lean-lang.md` Next Ten item 4). A row records "
        "both names with a verified source location, the equality regime on each "
        "side (this kernel is built from setoids and defined `Equiv`/`Apart` "
        "relations where Mathlib is a classical Cauchy or `Quot.sound` quotient "
        "-- ADR-0512, ADR-1588), a grade from a closed five-value enum, and at "
        "least one witness theorem pair for every grade except `no-counterpart`. "
        "A sentence anywhere in the docs claiming this library \"shares a "
        "theorem with Mathlib\" should cite a row here rather than assert it -- "
        "ADR-1665."
    )
    lines.append("")
    lines.append("## Counts by grade")
    lines.append("")
    lines.append("| Grade | Rows |")
    lines.append("|---|---:|")
    for g in GRADE_ORDER:
        lines.append(f"| {GRADE_LABEL[g]} (`{g}`) | {counts[g]} |")
    lines.append(f"| **Total** | **{len(rows)}** |")
    lines.append("")

    lines.append("## Rows")
    lines.append("")
    for row in sorted(rows, key=lambda r: r.get("id", "")):
        rid = row.get("id", "?")
        title = row.get("title", "")
        grade = row.get("grade", "?")
        axeyum = row.get("axeyum", {})
        mathlib = row.get("mathlib", {})
        lines.append(f"### `{rid}` -- {md_escape(title)}")
        lines.append("")
        lines.append(f"**Grade:** {GRADE_LABEL.get(grade, grade)} (`{grade}`)")
        lines.append("")
        lines.append(f"**Reason:** {md_escape(row.get('reason', ''))}")
        lines.append("")
        lines.append("| | Axeyum | Mathlib |")
        lines.append("|---|---|---|")
        lines.append(
            "| Carrier | {} | {} |".format(
                md_escape(str(axeyum.get("carrier", ""))),
                md_escape(str(mathlib.get("counterpart") or "*(none)*")),
            )
        )
        lines.append(
            "| Location | `{}` | `{}` |".format(
                axeyum.get("source_location") or "unverified",
                mathlib.get("source_location") or "n/a",
            )
        )
        lines.append(
            "| Verification | {} | {} |".format(
                axeyum.get("verification", "?"),
                mathlib.get("verification", "?"),
            )
        )
        lines.append(
            "| Equality regime | {} | {} |".format(
                axeyum.get("equality_regime", "?"),
                mathlib.get("equality_regime", "?"),
            )
        )
        lines.append("")
        witness = row.get("witness", [])
        if witness:
            lines.append("**Witness pairs:**")
            lines.append("")
            for w in witness:
                axth = w.get("axeyum_theorem", "?")
                mlth = w.get("mathlib_theorem")
                lines.append(
                    f"- `{axth}` vs {'`' + mlth + '`' if mlth else '*(no Mathlib counterpart for this pair)*'} "
                    f"-- {md_escape(w.get('note', ''))}"
                )
            lines.append("")
        notes = row.get("notes")
        if notes:
            lines.append(f"**Notes:** {md_escape(notes)}")
            lines.append("")

    lines.append("## How to re-measure")
    lines.append("")
    lines.append("```sh")
    lines.append("python3 scripts/check-carrier-correspondence.py --check")
    lines.append("python3 -m unittest scripts.tests.test_check_carrier_correspondence")
    lines.append("python3 scripts/gen-carrier-correspondence-md.py --check")
    lines.append("```")
    lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0] if __doc__ else "")
    parser.add_argument("--check", action="store_true", help="fail if the committed generated Markdown is stale")
    args = parser.parse_args()

    try:
        doc = load(LEDGER)
    except (OSError, ValueError) as exc:
        print(f"CARRIER_CORRESPONDENCE_MD_ERROR|cannot read {relative(LEDGER)}: {exc}", file=sys.stderr)
        return 1

    rendered = render(doc)
    if args.check:
        if not OUT_MD.is_file():
            print(f"missing generated file: {relative(OUT_MD)}", file=sys.stderr)
            return 1
        if OUT_MD.read_text(encoding="utf-8") != rendered:
            print(
                f"stale generated file: {relative(OUT_MD)}; run "
                "python3 scripts/gen-carrier-correspondence-md.py",
                file=sys.stderr,
            )
            return 1
    else:
        OUT_MD.parent.mkdir(parents=True, exist_ok=True)
        OUT_MD.write_text(rendered, encoding="utf-8")

    print(f"CARRIER_CORRESPONDENCE_MD|rows={len(doc.get('rows', []))}|checked={int(args.check)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
