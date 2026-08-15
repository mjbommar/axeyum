#!/usr/bin/env python3
"""Generate PLAN.md from hand-authored global sections plus per-lane files.

`PLAN.md` is the repository's canonical mutable tracker, and CLAUDE.md's session
protocol tells *every* lane to update it before ending a session.  That
instruction is why it was touched 67 times in 24 hours by concurrent lanes, and
why one lane's uncommitted edit was swept into another lane's commit on
2026-08-14.  Pathspec discipline cannot help: it stops you sweeping a file you
did not touch, not two lanes legitimately touching the same one.

So PLAN.md becomes a view.  Two kinds of source:

``docs/plan/global/*.md``
    The genuinely project-wide sections — the header, Status, the A1..A11
    queue, Workstream state, the resume protocol, the planning rules, the
    detail map, the consolidation record.  Hand-authored, emitted verbatim in
    filename order, joined by one blank line.  These are project-level
    statements, not lane statements; keeping them hand-authored is deliberate.
    Editing one is still a shared edit, but it is a *rare* one — the churn was
    in the lane blocks and the landed-changes table, and those are now split.

``docs/plan/status/*.md``
    One file per lane.  Nothing merges by hand.  Each contributes to named
    placeholders in the global sections::

        <!-- plan-section: lane-status -->     its block in "Next Actions"
        <!-- plan-section: landed-changes -->  its rows in the changes table

    and the matching global placeholders are::

        <!-- plan-generated: lane-status -->
        <!-- plan-generated: landed-changes -->

Landed-changes rows are merged newest-first across lanes, so two lanes landing
work on the same day never edit the same line.

Regenerate with ``python3 scripts/gen-plan.py``; ``--check`` fails when PLAN.md
differs from a fresh generation, which is what turns a hand edit into a gate
failure instead of somebody else's lost paragraph.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
GLOBAL_DIR = ROOT / "docs" / "plan" / "global"
STATUS_DIR = ROOT / "docs" / "plan" / "status"
OUTPUT = ROOT / "PLAN.md"

SECTIONS = ("lane-status", "landed-changes")
PLACEHOLDER = re.compile(r"^<!-- plan-generated: ([a-z-]+) -->$")
LANE_MARKER = re.compile(r"^<!-- plan-section: ([a-z-]+) -->$")
LANDED_ROW = re.compile(r"^\| (\d{4}-\d{2}-\d{2}) \| .* \|$")

# `scripts/check-plan-authority.py` fails closed on these.  Asserting them here
# too means a decomposition mistake is caught by the generator that made it,
# with the section name in hand, instead of three gates later.
REQUIRED_PLAN_MARKERS = (
    "Canonical project tracker",
    "## Status",
    "## Next Actions",
    "## Workstream state",
    "## Resume protocol",
    "## Planning rules",
)

BANNER = """> **Generated; do not edit by hand.** Sources: project-wide sections in
> [`docs/plan/global/`](docs/plan/global/README.md), one file per lane in
> [`docs/plan/status/`](docs/plan/status/README.md). Edit **your lane's file**
> and run `python3 scripts/gen-plan.py`; `--check` is a gate. This file was
> touched 67 times in 24 hours by concurrent lanes on 2026-08-13/14 and one
> lane's edit was swept into another's commit — that is what the split fixes."""


class PlanError(Exception):
    """A malformed source file: reported, never silently skipped."""


def display(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def read_lane(path: Path) -> dict[str, object]:
    """Split one lane file into its named contributions."""
    lines = path.read_text(encoding="utf-8").splitlines()
    heading = lines[0] if lines else ""
    if not heading.startswith("# "):
        raise PlanError(f"{display(path)}: first line must be a '# ' heading naming the lane")

    contributions: dict[str, list[str]] = {}
    current: str | None = None
    for number, line in enumerate(lines[1:], start=2):
        marker = LANE_MARKER.match(line)
        if marker is not None:
            name = marker.group(1)
            if name not in SECTIONS:
                raise PlanError(
                    f"{display(path)}:{number}: unknown section {name!r}; "
                    f"known sections are {', '.join(SECTIONS)}"
                )
            if name in contributions:
                raise PlanError(f"{display(path)}:{number}: section {name!r} appears twice")
            contributions[name] = []
            current = name
            continue
        if current is None:
            if line.strip():
                raise PlanError(
                    f"{display(path)}:{number}: text before the first "
                    "'<!-- plan-section: ... -->' marker would never be emitted"
                )
            continue
        contributions[current].append(line)

    return {
        "path": path.name,
        "lane": path.stem,
        "sections": {
            name: rebase_links("\n".join(body).strip("\n"), path)
            for name, body in contributions.items()
        },
    }


# A relative link is relative to the file it lives in, and generation moves the
# text to a different directory. `docs/plan/status/x.md` writing
# `../../mathematics-2026-08/y.md` is correct where it sits and escapes the
# repository once emitted into `PLAN.md` at the root.
#
# This is not hypothetical: it shipped, broke `check-links.sh`, and two separate
# lanes each declined to fix it because the file belonged to the other. The fix
# belongs in the generator, not in a convention every future lane must remember —
# a source file should be correct in its own right AND survive being moved.
RELATIVE_LINK = re.compile(r"(?<=\]\()(?!https?://|#|/)([^)]+)(?=\))")


def rebase_links(body: str, source: Path) -> str:
    """Rewrite relative markdown links so they resolve from `PLAN.md` at the root."""

    def rebase(match: re.Match[str]) -> str:
        target = match.group(1)
        anchor = ""
        if "#" in target:
            target, _, anchor = target.partition("#")
            anchor = "#" + anchor
        if not target:
            return match.group(0)
        # Two conventions are already in use and they are not distinguishable by
        # syntax: some status files write links relative to themselves
        # (`../../mathematics-2026-08/x.md`), others write them already relative to
        # the repository root, for `PLAN.md`'s benefit (`docs/plan/x.md`).
        # Rewriting the second kind produced `docs/plan/status/docs/plan/...` on the
        # first attempt here. So ask the filesystem instead of guessing: rebase only
        # what actually resolves against the source file's own directory.
        from_source = (source.parent / target).resolve()
        if from_source.exists():
            try:
                return str(from_source.relative_to(ROOT)) + anchor
            except ValueError:
                return match.group(0)  # outside the repo; report, do not invent
        # Already root-relative, or simply broken. Either way leave it exactly as
        # written and let `check-links.sh` be the one to complain.
        return match.group(0)

    return RELATIVE_LINK.sub(rebase, body)


def _negated_date(date: str) -> str:
    """Sort key giving newest-first over ISO dates without a datetime parse."""
    return "".join(chr(ord("9") - int(char)) if char.isdigit() else char for char in date)


def landed_sort_key(row: dict[str, object]) -> tuple[str, str, int]:
    """Newest first; ties broken by lane, then by order within that lane's file.

    Without the lane/ordinal tiebreak, same-day rows from different lanes come
    back in whatever order the filesystem produced — the merge would not be
    reproducible, which is the property the whole exercise is about.
    """
    return (_negated_date(str(row["date"])), str(row["lane"]), int(row["ordinal"]))


def collect_landed(lanes: list[dict[str, object]]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for lane in lanes:
        sections: dict[str, str] = lane["sections"]  # type: ignore[assignment]
        body = sections.get("landed-changes", "")
        for ordinal, line in enumerate(body.splitlines()):
            if not line.strip():
                continue
            row = LANDED_ROW.match(line)
            if row is None:
                raise PlanError(
                    f"{lane['path']}: landed-changes row is not "
                    f"'| YYYY-MM-DD | … | … |': {line!r}"
                )
            rows.append(
                {
                    "date": row.group(1),
                    "lane": lane["lane"],
                    "ordinal": ordinal,
                    "text": line,
                }
            )
    rows.sort(key=landed_sort_key)
    return rows


def render(global_parts: list[tuple[str, str]], lanes: list[dict[str, object]]) -> str:
    if not global_parts:
        raise PlanError(f"no global sections under {display(GLOBAL_DIR)}")

    blocks = {
        "lane-status": "\n\n".join(
            body
            for lane in lanes
            if (body := str(lane["sections"].get("lane-status", "")).strip("\n"))  # type: ignore[union-attr]
        ),
        "landed-changes": "\n".join(
            str(row["text"]) for row in collect_landed(lanes)
        ),
    }

    seen: set[str] = set()
    rendered_parts: list[str] = []
    for name, text in global_parts:
        out: list[str] = []
        for number, line in enumerate(text.rstrip("\n").splitlines(), start=1):
            placeholder = PLACEHOLDER.match(line)
            if placeholder is None:
                out.append(line)
                continue
            section = placeholder.group(1)
            if section not in SECTIONS:
                raise PlanError(
                    f"{name}:{number}: unknown placeholder {section!r}; "
                    f"known sections are {', '.join(SECTIONS)}"
                )
            if section in seen:
                raise PlanError(f"{name}:{number}: placeholder {section!r} already used")
            seen.add(section)
            out.append(blocks[section])
        rendered_parts.append("\n".join(out))

    for name in SECTIONS:
        if name not in seen:
            raise PlanError(
                f"no '<!-- plan-generated: {name} -->' placeholder in "
                f"{display(GLOBAL_DIR)}; every lane's {name} would be dropped"
            )

    body = rendered_parts[0].splitlines()
    if not body or not body[0].startswith("# "):
        raise PlanError(f"{global_parts[0][0]}: must start with PLAN.md's level-1 heading")
    rendered_parts[0] = "\n".join([body[0], "", BANNER, *body[1:]])

    rendered = "\n\n".join(rendered_parts) + "\n"
    for marker in REQUIRED_PLAN_MARKERS:
        if marker not in rendered:
            raise PlanError(
                f"generated PLAN.md is missing {marker!r}, which "
                "scripts/check-plan-authority.py requires"
            )
    return rendered


def load() -> tuple[list[tuple[str, str]], list[dict[str, object]]]:
    global_parts = [
        (path.name, path.read_text(encoding="utf-8"))
        for path in sorted(GLOBAL_DIR.glob("*.md"))
        if path.name != "README.md"
    ]
    candidates = [p for p in sorted(STATUS_DIR.glob("*.md")) if p.name != "README.md"]
    tracked, untracked = partition_tracked(candidates)
    if untracked:
        # Not silent: a lane whose file is skipped must be able to see why.
        print(
            "gen-plan: skipping "
            + ", ".join(display(p) for p in untracked)
            + " (untracked; `git add` them to include them)",
            file=sys.stderr,
        )
    return global_parts, [read_lane(path) for path in tracked]


def partition_tracked(paths: list[Path]) -> tuple[list[Path], list[Path]]:
    """Split status files into git-tracked and not.

    PLAN.md is generated by rolling up EVERY lane's status file, and the roll-up
    is committed. Globbing the filesystem therefore folds another lane's
    *uncommitted* narrative into whoever regenerates next, and it happened twice
    in one day: one lane found its block in another lane's commit, and a second
    lane worked around it by regenerating from a `git archive` snapshot in a temp
    directory. That workaround is the correct instinct and should not be needed.

    Reading tracked state instead makes the roll-up a function of what is
    committed, which is what the file it produces is. A lane's first status file
    simply needs `git add` before it appears -- an explicit step, and a cheap one
    next to publishing someone else's unfinished text under your name.

    A checkout without git, or one where the query fails, degrades to including
    everything: this is a convenience guard, never a correctness gate, and it
    must not make the generator unusable.
    """
    try:
        result = subprocess.run(
            ["git", "ls-files", "--error-unmatch", "--", *[str(p) for p in paths]],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError:
        return paths, []
    if result.returncode != 0 and not result.stdout.strip():
        return paths, []
    listed = {line.strip() for line in result.stdout.splitlines() if line.strip()}
    tracked, untracked = [], []
    for path in paths:
        rel = str(path.relative_to(ROOT))
        (tracked if rel in listed else untracked).append(path)
    return tracked, untracked


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail when the committed PLAN.md differs from a fresh generation",
    )
    args = parser.parse_args()

    try:
        global_parts, lanes = load()
        rendered = render(global_parts, lanes)
    except (PlanError, FileNotFoundError) as error:
        print(f"gen-plan: ERROR: {error}", file=sys.stderr)
        return 1

    if args.check:
        current = OUTPUT.read_text(encoding="utf-8") if OUTPUT.is_file() else None
        if current != rendered:
            print(
                f"gen-plan: ERROR: {display(OUTPUT)} is not what scripts/gen-plan.py "
                "produces. It is generated: put your change in your lane's file under "
                "docs/plan/status/ (or the relevant docs/plan/global/ section) and "
                "rerun the generator.",
                file=sys.stderr,
            )
            return 1
    else:
        OUTPUT.write_text(rendered, encoding="utf-8")

    landed = collect_landed(lanes)
    print(
        "PLAN|"
        f"global_sections={len(global_parts)}|"
        f"lanes={len(lanes)}|"
        f"lane_blocks={sum('lane-status' in lane['sections'] for lane in lanes)}|"  # type: ignore[operator]
        f"landed_rows={len(landed)}|"
        f"bytes={len(rendered.encode('utf-8'))}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
