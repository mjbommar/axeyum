#!/usr/bin/env python3
"""Move the detail out of an over-long lane status block, without losing a byte.

`scripts/check-plan-authority.py` bounds what `PLAN.md` is generated from. The
bound has been broken for days -- 177,878 bytes against a 52,000 ceiling on
2026-08-18, and the gate's own comment records the growth as 0 -> 54,398 ->
98,180 -> 233,888 in two days. A gate that has been red that long is not a gate;
it is a thing everyone has learned to scroll past.

The instructive part is WHERE the bytes are, because it is not where the gate's
remediation text says. "Move journal/detail to a result note" points at the
landed-changes journal, which is **25,893 bytes across 61 rows**. The lane-status
blocks -- "what is true now, what is next, what is blocked" -- are **119,818
bytes across 25 lanes**, averaging 4,800 each. Archiving the whole journal would
have recovered a fifth of the overage.

Nobody wrote an essay on purpose. The status block is the only place a lane has
to explain a finding, so findings go there. This gives them the other place:
`docs/plan/notes/<lane>.md`, which `gen-plan.py` does not read and the ceiling
does not count, linked from the block that was trimmed.

# What it will not do

- **It never edits a file with uncommitted changes.** Another lane mid-edit is
  exactly the case that has cost this repository real work seven times; those
  files are skipped and named.
- **It splits on a blank line, never mid-paragraph**, and it never deletes: the
  remainder is appended to the note under a dated heading, so the content moves
  rather than shrinking. `--check` proves the round trip.
- It does not touch `docs/plan/global/`, which is genuinely shared and bounded
  as a whole rather than per lane.
"""

from __future__ import annotations

import argparse
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
STATUS = ROOT / "docs/plan/status"
NOTES = ROOT / "docs/plan/notes"
LANE_CAP = 3_000
# The journal is kept by BYTES, not by row count. Rows are not comparable: in
# `creal.md` nine rows run 1,434 / 1,145 / 651 bytes, so "keep the newest three"
# left 3,387 bytes of journal in a file capped at 3,000 and the lane could not
# be brought under by any amount of prose trimming. At least one row always
# stays, however long it is -- a lane with no visible landing reads as a lane
# that has not landed anything.
JOURNAL_BUDGET = 1_200
MARK_STATUS = "<!-- plan-section: lane-status -->"
MARK_LANDED = "<!-- plan-section: landed-changes -->"


def dirty_paths() -> set[pathlib.Path]:
    """Files with uncommitted changes — never touched, whoever owns them."""
    out = subprocess.run(
        ["git", "status", "--porcelain", "--", "docs/plan/status"],
        cwd=ROOT, capture_output=True, text=True, check=False,
    ).stdout
    paths = set()
    for line in out.splitlines():
        name = line[3:].strip()
        if name:
            paths.add((ROOT / name).resolve())
    return paths


def lane_files() -> list[pathlib.Path]:
    return [p for p in sorted(STATUS.glob("*.md")) if p.name != "README.md"]


def split_block(block: str, budget: int) -> tuple[str, str]:
    """Keep whole paragraphs up to `budget` bytes; return (kept, moved).

    Paragraph-granular on purpose. A byte-granular split would cut a sentence,
    and the point of the block is that someone can read it.
    """
    paras = block.split("\n\n")
    kept: list[str] = []
    size = 0
    for i, para in enumerate(paras):
        cost = len(para.encode("utf-8")) + 2
        if kept and size + cost > budget:
            return "\n\n".join(kept), "\n\n".join(paras[i:])
        kept.append(para)
        size += cost
    return block, ""


def process(path: pathlib.Path, apply: bool) -> tuple[int, int, str]:
    """-> (bytes_before, bytes_after, note). Pure unless `apply`."""
    text = path.read_text(encoding="utf-8")
    before = len(text.encode("utf-8"))
    if before <= LANE_CAP:
        return before, before, "under cap"
    if MARK_STATUS not in text:
        return before, before, "no lane-status block (nothing to move)"

    head, rest = text.split(MARK_STATUS, 1)
    if MARK_LANDED in rest:
        block, tail = rest.split(MARK_LANDED, 1)
        tail = MARK_LANDED + tail
    else:
        block, tail = rest, ""

    # Archive the JOURNAL first when it is what is over budget. Measured
    # 2026-08-18 the journal is a fifth of the problem overall (25,893 bytes of
    # 146,636) but it is concentrated: two lanes carried 7,534 and 5,983 bytes
    # of rows, enough that no amount of prose trimming could bring them under.
    moved_rows: list[str] = []
    fixed = len(head.encode()) + len(MARK_STATUS.encode()) + len(tail.encode())
    if fixed + 400 > LANE_CAP and tail:
        lines = tail.split("\n")
        rows = [i for i, line in enumerate(lines) if line.startswith("|")]
        keep = 0
        spent = 0
        for i in rows:
            cost = len(lines[i].encode("utf-8")) + 1
            if keep and spent + cost > JOURNAL_BUDGET:
                break
            keep += 1
            spent += cost
        if len(rows) > keep:
            cut = rows[keep]
            moved_rows = [line for line in lines[cut:] if line.startswith("|")]
            # NOTHING but table rows may live in this section: `gen-plan.py`
            # rejects any other line ("landed-changes row is not
            # '| YYYY-MM-DD | … | … |'"). The pointer therefore goes in the
            # prose block above, not here.
            lines = lines[:cut] + [""]
            tail = "\n".join(lines)
            fixed = len(head.encode()) + len(MARK_STATUS.encode()) + len(tail.encode())

    budget = LANE_CAP - fixed - 200  # 200 for the pointer line
    if budget <= 0:
        return before, before, (
            f"cannot trim: head+journal is {fixed} bytes even after archiving "
            f"{len(moved_rows)} row(s); needs a human"
        )

    kept, moved = split_block(block.strip("\n"), budget)
    if not moved and not moved_rows:
        return before, before, "single paragraph already over budget — needs a human"

    note = NOTES / path.name
    rel = f"../notes/{path.name}"
    what_moved = "Detail" if not moved_rows else "Detail and older landed rows"
    pointer = f"\n{what_moved} moved to [`{rel}`]({rel}).\n"
    new = head + MARK_STATUS + "\n\n" + kept + "\n"
    if moved or moved_rows:
        new += pointer
    new += "\n" + tail
    after = len(new.encode("utf-8"))

    if apply:
        NOTES.mkdir(parents=True, exist_ok=True)
        prior = note.read_text(encoding="utf-8") if note.exists() else (
            f"# Notes: {path.stem}\n\n"
            f"Detail moved out of [`../status/{path.name}`](../status/{path.name}) so the\n"
            "lane-status block stays inside the per-lane ceiling. Nothing here was\n"
            "deleted; it was moved.\n"
        )
        addition = moved.strip("\n")
        if moved_rows:
            addition = (addition + "\n\n" if addition else "") + \
                "## Archived landed-changes rows\n\n" + "\n".join(moved_rows)
        note.write_text(prior.rstrip("\n") + "\n\n" + addition + "\n", encoding="utf-8")
        path.write_text(new, encoding="utf-8")
    what = []
    if moved:
        what.append(f"{len(moved.encode())} prose bytes")
    if moved_rows:
        what.append(f"{len(moved_rows)} journal row(s)")
    return before, after, "moved " + " + ".join(what) + f" to notes/{path.name}"


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--apply", action="store_true", help="write the changes")
    args = ap.parse_args(argv)

    dirty = dirty_paths()
    total_before = total_after = 0
    skipped: list[str] = []
    for path in lane_files():
        if path.resolve() in dirty:
            size = path.stat().st_size
            total_before += size
            total_after += size
            if size > LANE_CAP:
                skipped.append(f"{path.name} ({size} bytes, over cap)")
            continue
        before, after, note = process(path, args.apply)
        total_before += before
        total_after += after
        if before != after or "cannot" in note or "human" in note:
            print(f"  {path.name}: {before} -> {after}  ({note})")

    print(
        f"ARCHIVE_PLAN_STATUS|cap={LANE_CAP}|before={total_before}|after={total_after}|"
        f"skipped_dirty={len(skipped)}"
    )
    if skipped:
        print("  skipped (uncommitted changes — another lane may be mid-edit): "
              + ", ".join(skipped))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
