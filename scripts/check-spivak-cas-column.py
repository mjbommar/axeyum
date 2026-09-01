#!/usr/bin/env python3
"""Gate: every Spivak spine row states a CAS (ADR-0603 row 3) verdict.

WHY THIS EXISTS
---------------
Asked how much of Spivak *Calculus* is complete, the coordinator read
`docs/curriculum/foundational-books/spivak.md`'s route column -- whose legend
read "Three routes, not two: S / K / X", with the string ``axeyum-cas`` appearing
exactly ONCE in the file -- and reported the ``X`` rows as terminal.  They are
not: ``X`` is ADR-0603 **row 1**'s verdict, and the CAS supplies **row 3**, the
exact classical statement on the decidable fragment.  Chapter 20 read
``| 20 | Taylor polynomials | - | open |`` while
``crates/axeyum-cas/src/taylor.rs`` shipped Taylor's theorem with the Lagrange
remainder, naming ADR-0603 row 3 and Spivak ch. 20 in its own module doc.
Chapter 19 had no row at all.

A prose fix decays.  This gate makes the omission mechanically impossible in the
one direction that caused the error: a row may say the CAS reaches something, or
say it was checked and reaches nothing, but it may not stay SILENT.

WHAT IT CHECKS, AND WHY EACH GUARD IS SEPARATE
----------------------------------------------
Each guard below fails on a defect the others cannot see.  They are deliberately
not folded into one predicate: CLAUDE.md records a suite where six of seven
guards were removable with everything still green, because all seven rejected
through one shared check.

R1  the table exists at all, with the ``C`` column in its header.  Without this
    every later guard would pass vacuously over zero rows -- the
    checker-that-cannot-fail defect, arriving through an empty iteration.

R2  every row has exactly the header's cell count.  A hand-edited row that drops
    a pipe silently shifts ``State`` into the ``C`` position, so a later guard
    would read prose about the kernel as if it were a CAS verdict.

R3  no ``C`` cell is empty or a bare dash.  This is the original defect.

R4  a ``C`` cell that reports nothing must carry the explicit audited-none
    marker.  "Audited, and the CAS reaches nothing here" and "nobody looked" are
    different findings and must not read identically -- the distinction this
    whole gate exists to preserve.

R5  a ``C`` cell that is NOT audited-none must name something in the CAS:
    a ``crate::module`` path, a ``module.rs`` file, or a ledger fact id.  A cell
    saying only "yes the CAS can do this" is not an audit finding.

R6  the chapter column must cover 1..30 with no gap.  Chapter 19 was missing for
    the life of the table and nothing noticed, because a gap in a hand-written
    list is invisible to any per-row check.

R7  every ledger fact id a ``C`` cell cites must exist in ``artifacts/facts/``
    and carry ``proof_route == "cas-certificate"``.  A cell citing a fact that
    was renamed, or citing a kernel fact as if it were CAS evidence, is exactly
    the overclaim ADR-0601 forbids.

R8  the legend must not still advertise three routes.  The header sentence is
    what the coordinator actually read; leaving it stale while the table is
    correct reproduces the original failure for the next reader.

Exit 0 when every guard passes, 1 on any failure (naming the row), 2 on a usage
error.  ``--check`` is accepted and ignored, for symmetry with the other gates.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

DEFAULT_DOC = Path("docs/curriculum/foundational-books/spivak.md")
DEFAULT_FACTS = Path("artifacts/facts")

HEADER_START = "| Spivak | Topic | Route |"
# The marker a row uses to say "checked, and the CAS reaches nothing here".
AUDITED_NONE = "audited — none"
# An audited-none cell must carry at least this much explanation beyond the
# marker itself. Every real one in the file runs to several sentences; the bar
# is set low deliberately, since the guard is against a bare label, not against
# terseness.
MIN_REASON_CHARS = 40
# What counts as naming a concrete CAS artifact.
NAMES_ARTIFACT = re.compile(
    r"[a-z_0-9]+::[A-Za-z_0-9{]"   # crate-internal path, e.g. taylor::polynomial_taylor
    r"|[a-z_0-9]+\.rs"             # a module file, e.g. ratint.rs
    r"|`F:[a-z0-9-]+`"             # a ledger fact id
)
FACT_ID = re.compile(r"`(F:[a-z0-9-]+)`")
# Chapter labels are "7", "3–4" (en dash), "22–23"; markdown bold is stripped first.
CHAPTER_SPAN = re.compile(r"^(\d+)(?:[–-](\d+))?$")


def fail(errors: list[str], msg: str) -> None:
    errors.append(msg)


def strip_bold(text: str) -> str:
    return text.replace("**", "").strip()


def split_row(row: str) -> list[str]:
    """Split a markdown table row into its cells.

    The row is ``| a | b | c |``.  Stripping the outer pipes and splitting on
    ``" | "`` is correct here because every cell in this table is prose that
    escapes its own pipes (``\\|a+b\\|``), which is the file's existing
    convention and is what makes a naive split safe.
    """
    body = row.strip()
    assert body.startswith("|") and body.endswith("|")
    return [c.strip() for c in body[1:-1].split(" | ")]


def find_table(lines: list[str]) -> tuple[int, list[str]] | None:
    for i, line in enumerate(lines):
        if line.startswith(HEADER_START):
            header = split_row(line)
            rows = []
            j = i + 2  # skip the |---| separator
            while j < len(lines) and lines[j].startswith("|"):
                rows.append(lines[j])
                j += 1
            return i, [line] + rows
    return None


def known_cas_fact_ids(facts_dir: Path) -> set[str]:
    ids: set[str] = set()
    for path in sorted(facts_dir.glob("*.json")):
        try:
            fact = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if fact.get("proof_route") == "cas-certificate":
            fid = fact.get("id")
            if isinstance(fid, str):
                ids.add(fid)
    return ids


def check(doc: Path, facts_dir: Path) -> list[str]:
    errors: list[str] = []
    text = doc.read_text(encoding="utf-8")
    lines = text.split("\n")

    found = find_table(lines)
    if found is None:
        # R1
        fail(errors, f"{doc}: no spine table found (no line starting {HEADER_START!r})")
        return errors
    start, table = found
    header, rows = split_row(table[0]), table[1:]

    if not any(cell.startswith("C ") or cell == "C" for cell in header):
        # R1
        fail(errors, f"{doc}:{start + 1}: spine table header has no `C` column: {header!r}")
        return errors
    c_index = next(i for i, cell in enumerate(header) if cell.startswith("C ") or cell == "C")

    if not rows:
        # R1 -- an empty table would let every guard below pass vacuously.
        fail(errors, f"{doc}:{start + 1}: spine table has zero rows")
        return errors

    cas_ids = known_cas_fact_ids(facts_dir)
    seen_chapters: set[int] = set()

    for offset, row in enumerate(rows):
        lineno = start + 3 + offset
        cells = split_row(row)
        label = strip_bold(cells[0]) if cells else "?"

        if len(cells) != len(header):
            # R2
            fail(errors, f"{doc}:{lineno}: row {label!r} has {len(cells)} cells, "
                         f"header has {len(header)}")
            continue

        # R6 -- record which chapters this row covers.
        span = CHAPTER_SPAN.match(label)
        if span is None:
            fail(errors, f"{doc}:{lineno}: chapter label {label!r} is not a number or a span")
        else:
            lo = int(span.group(1))
            hi = int(span.group(2)) if span.group(2) else lo
            seen_chapters.update(range(lo, hi + 1))

        cell = cells[c_index]
        bare = strip_bold(cell)

        if not bare or bare in {"-", "—", "–", "?", "TBD", "UNAUDITED"}:
            # R3
            fail(errors, f"{doc}:{lineno}: chapter {label} has an EMPTY `C` cell "
                         f"({cell!r}). A blank C is UNAUDITED, which is the defect this "
                         f"gate exists to prevent -- write the finding, or the explicit "
                         f"marker {AUDITED_NONE!r}.")
            continue

        has_marker = AUDITED_NONE in cell
        names_artifact = NAMES_ARTIFACT.search(cell) is not None

        if has_marker:
            # R4 -- an audited-none finding must say WHY the CAS reaches nothing.
            # Bare "audited -- none." is a label, not a measurement, and it is
            # exactly as unfalsifiable as the blank cell R3 rejects.
            reason = bare.replace(AUDITED_NONE, "").strip(" .-—–*")
            if len(reason) < MIN_REASON_CHARS:
                fail(errors, f"{doc}:{lineno}: chapter {label}'s `C` cell carries the "
                             f"{AUDITED_NONE!r} marker with no reason ({len(reason)} chars "
                             f"of explanation, need {MIN_REASON_CHARS}). An unexplained "
                             f"'none' is as unfalsifiable as a blank cell.")
        elif not names_artifact:
            # R5 -- a cell asserting a CAS route must name what it consulted.
            fail(errors, f"{doc}:{lineno}: chapter {label}'s `C` cell asserts a CAS route "
                         f"but names no module, function or fact id. Cite "
                         f"`module::function`, a `module.rs`, or a `F:...` fact -- "
                         f"or say {AUDITED_NONE!r}.")

        for fid in FACT_ID.findall(cell):
            if fid not in cas_ids:
                # R7
                fail(errors, f"{doc}:{lineno}: chapter {label}'s `C` cell cites {fid}, "
                             f"which is not a fact with proof_route == 'cas-certificate' "
                             f"under {facts_dir}/")

    # R6
    missing = sorted(set(range(1, 31)) - seen_chapters)
    if missing:
        fail(errors, f"{doc}: spine table has no row for Spivak chapter(s) "
                     f"{', '.join(str(m) for m in missing)}. Chapter 19 was absent for "
                     f"the life of this table while `partial_fractions.rs` named it "
                     f"explicitly; a gap in a hand-written list is invisible per-row.")

    # R8
    if re.search(r"Three routes, not two", text):
        fail(errors, f"{doc}: the legend still says 'Three routes, not two'. That "
                     f"sentence is what produced the original wrong answer; the table "
                     f"having a `C` column does not repair it.")

    return errors


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--doc", type=Path, default=DEFAULT_DOC)
    parser.add_argument("--facts", type=Path, default=DEFAULT_FACTS)
    parser.add_argument("--check", action="store_true",
                        help="accepted and ignored; this gate never rewrites")
    args = parser.parse_args(argv)

    if not args.doc.is_file():
        print(f"check-spivak-cas-column: no such file: {args.doc}", file=sys.stderr)
        return 2
    if not args.facts.is_dir():
        print(f"check-spivak-cas-column: no such directory: {args.facts}", file=sys.stderr)
        return 2

    errors = check(args.doc, args.facts)
    if errors:
        for err in errors:
            print(f"FAIL {err}")
        print(f"\ncheck-spivak-cas-column: {len(errors)} failure(s)")
        return 1
    print("check-spivak-cas-column: OK -- every spine row states a CAS verdict")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
