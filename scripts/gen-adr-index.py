#!/usr/bin/env python3
"""Generate the ADR index from the ADR files themselves.

``docs/research/09-decisions/README.md`` used to be hand-appended: every ADR
added a row, and the file was touched 60 times in 24 hours by concurrent lanes.
Two of those appends were silently overwritten on 2026-08-14.  An index is a
*view*, so it is derived here instead of maintained.

Sources, all per-ADR so that two lanes writing two ADRs never edit one file:

* ``README-preamble.md`` — the hand-authored purpose/process/template prose,
  emitted verbatim ahead of the generated table.
* every ``adr-NNNN-*.md`` — its ``# ADR-NNNN: Title`` heading plus the
  ``Key: value`` front-matter block that follows it.

Front matter keys this reads:

``Status``
    Required.  The ADR's own status line.
``Index-summary``
    Optional.  The index row's title cell when the ADR's own heading is not the
    text the index should carry.  363 of the 454 rows carried a curated summary
    that existed *only* in the hand-maintained index; migrating them into the
    ADRs is what makes this generator lossless.
``Index-status``
    Optional.  The index row's status cell when the ADR's ``Status`` line is
    qualified ("accepted (equality slice implemented …)") but the index cell is
    the bare verdict.

Regenerate with ``python3 scripts/gen-adr-index.py``; ``--check`` fails when the
committed file differs from a fresh generation, which is what makes a hand edit
a gate failure rather than a lost line.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
DECISIONS = ROOT / "docs" / "research" / "09-decisions"
PREAMBLE = DECISIONS / "README-preamble.md"
OUTPUT = DECISIONS / "README.md"

HEADING = re.compile(r"^# ADR-(\d{4}):[ \t]*(.+?)[ \t]*$")
# Three front-matter styles are in the tree and all nine of the bullet-list
# ones were invisible to a naive '^Status:' scan: "Status: accepted",
# "- Status: proposed", and "- **Status:** accepted".
FRONT_MATTER = re.compile(
    r"^(?:-[ \t]+)?(?:\*\*)?([A-Za-z][A-Za-z0-9-]*)(?:\*\*)?:(?:\*\*)?[ \t]*(.*?)[ \t]*$"
)

BANNER = (
    "> **Generated; do not edit by hand.** Every row is derived from the "
    "`adr-*.md` file it links to (its heading, `Status:`, and optional "
    "`Index-summary:` / `Index-status:` front matter) plus the hand-authored "
    "[`README-preamble.md`](README-preamble.md). Regenerate with "
    "`python3 scripts/gen-adr-index.py`; `--check` is a gate. Editing this file "
    "directly is how index rows got silently overwritten twice on 2026-08-14."
)


class AdrError(Exception):
    """A malformed ADR file: reported, never silently skipped."""


def display(path: Path) -> str:
    """Repo-relative when possible; `relative_to` raises on anything else."""
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def parse_adr(path: Path) -> dict[str, str]:
    """Read one ADR's number, heading title, and front-matter block."""
    lines = path.read_text(encoding="utf-8").splitlines()
    heading = HEADING.match(lines[0]) if lines else None
    if heading is None:
        raise AdrError(f"{path.name}: first line is not '# ADR-NNNN: Title'")
    number, title = heading.group(1), heading.group(2)

    front: dict[str, str] = {}
    index = 1
    while index < len(lines) and not lines[index].strip():
        index += 1
    # The front matter is the run of `Key: value` lines that starts the file.
    # The first line that is not one -- a blank line, or the prose continuation
    # ADR-0059 puts between its `Index-status:` and `Date:` -- ends it.
    #
    # This stop is load-bearing, not tidiness: ADR bodies quote the template
    # ("Status: proposed | accepted | ...") and several discuss `Index-summary`
    # by name, so a whole-file scan reads prose as metadata and rewrites the
    # row from a sentence that was only ever an example.
    while index < len(lines):
        field = FRONT_MATTER.match(lines[index])
        if field is None:
            break
        front[field.group(1)] = field.group(2)
        index += 1

    if "Status" not in front:
        raise AdrError(f"{path.name}: no 'Status:' line in its front matter")

    row_title = front.get("Index-summary") or title
    row_status = front.get("Index-status") or front["Status"]
    for label, cell in (("title", row_title), ("status", row_status)):
        if "|" in cell:
            raise AdrError(
                f"{path.name}: {label} contains '|', which would break the table row"
            )

    return {
        "number": number,
        "path": path.name,
        "title": row_title,
        "status": row_status,
        "curated": "yes" if "Index-summary" in front else "no",
    }


def row_sort_key(adr: dict[str, str]) -> tuple[str, str]:
    """Total order over rows.

    ADR numbers are *not* unique — `0166` and `0167` name two ADRs each — so
    sorting on the number alone leaves those rows in whatever order the
    filesystem handed them over, which is not reproducible.  The filename is
    the tiebreak.
    """
    return (adr["number"], adr["path"])


def collect() -> list[dict[str, str]]:
    adrs = [parse_adr(path) for path in DECISIONS.glob("adr-*.md")]
    if not adrs:
        raise AdrError(f"no adr-*.md files under {DECISIONS}")
    adrs.sort(key=row_sort_key)
    return adrs


def render(preamble: str, adrs: list[dict[str, str]]) -> str:
    if "## Index" in preamble:
        raise AdrError(
            f"{PREAMBLE.name} contains its own '## Index' heading; the index is generated"
        )
    body = preamble.rstrip("\n").splitlines()
    if not body or not body[0].startswith("# "):
        raise AdrError(f"{PREAMBLE.name} must start with a level-1 heading")

    out = [body[0], "", BANNER, *body[1:], "", "## Index", "", "| ADR | Title | Status |", "|---|---|---|"]
    out.extend(
        f"| [{adr['number']}]({adr['path']}) | {adr['title']} | {adr['status']} |"
        for adr in adrs
    )
    return "\n".join(out) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail when the committed index differs from a fresh generation",
    )
    args = parser.parse_args()

    try:
        adrs = collect()
        rendered = render(PREAMBLE.read_text(encoding="utf-8"), adrs)
    except (AdrError, FileNotFoundError) as error:
        print(f"adr-index: ERROR: {error}", file=sys.stderr)
        return 1

    if args.check:
        current = OUTPUT.read_text(encoding="utf-8") if OUTPUT.is_file() else None
        if current != rendered:
            print(
                f"adr-index: ERROR: {display(OUTPUT)} is not what "
                "scripts/gen-adr-index.py produces. It is generated: put the change "
                "in the ADR file (or README-preamble.md) and rerun the generator.",
                file=sys.stderr,
            )
            return 1
    else:
        OUTPUT.write_text(rendered, encoding="utf-8")

    duplicates = sorted(
        number
        for number, count in Counter(adr["number"] for adr in adrs).items()
        if count > 1
    )
    print(
        "ADR_INDEX|"
        f"rows={len(adrs)}|"
        f"curated_summaries={sum(adr['curated'] == 'yes' for adr in adrs)}|"
        f"duplicate_numbers={','.join(duplicates) if duplicates else 'none'}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
