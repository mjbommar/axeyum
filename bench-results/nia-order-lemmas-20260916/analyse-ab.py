#!/usr/bin/env python3
"""Read ADR-2136's interleaved A/B rows: coverage, disagreements, movers.

Three questions, in the order that matters, and the exit status depends on the
answer to the first two:

1. **Coverage.** How many rows did each arm actually produce a verdict line
   for, against the list's own length. A sweep that silently dropped files is a
   measurement of the subset that survived, not of the division -- and an
   analysis that prints percentages over whatever rows it found cannot tell the
   difference.
2. **Disagreements.** Rows where one arm says `sat` and the other `unsat`.
   There is no ambient-noise story for this: the two arms are the same binary
   on the same file, so one of them is wrong. ANY nonzero count is a soundness
   finding and this script exits nonzero for it.
3. **Movers.** Rows where exactly one arm DECIDED. Both directions in one list,
   because a re-check that only carried the losses would make the gains
   unverifiable by the same method. A raw mover is a candidate: a single
   interleaved pairing at 24 s carries a measured 1-1.5 % ambient flip rate on
   these boxes, and ADR-1966 saw 11 of 18 out-of-division movers vanish on
   re-check.

Usage:
    python3 analyse-ab.py --list-dir DIR --movers-out LIST <tsv>...
"""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path

DECIDED = {"sat", "unsat"}


def division_of(tsv: Path) -> str:
    name = tsv.stem
    return name[3:] if name.startswith("ab-") else name


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--list-dir", required=True, help="where ab-list-<DIV>.txt live")
    ap.add_argument("--movers-out", required=True)
    ap.add_argument("tsv", nargs="+")
    args = ap.parse_args()

    movers: list[tuple[str, str, str, str]] = []
    disagreements: list[tuple[str, str, str, str]] = []
    bad_coverage = 0
    print("division            list   rows   A-dec   B-dec   none/err")
    for path in map(Path, args.tsv):
        div = division_of(path)
        listing = Path(args.list_dir) / f"ab-list-{div}.txt"
        expected = (
            sum(1 for line in listing.read_text().splitlines() if line.strip())
            if listing.exists()
            else None
        )
        rows = 0
        a_dec = b_dec = 0
        errors = 0
        for line in path.read_text(encoding="utf-8").splitlines():
            cells = line.split("\t")
            if not cells or cells[0] == "file":
                continue
            if len(cells) != 9:
                errors += 1
                continue
            rows += 1
            f, a, b = cells[0], cells[1], cells[4]
            a_dec += a in DECIDED
            b_dec += b in DECIDED
            if a in DECIDED and b in DECIDED and a != b:
                disagreements.append((div, f, a, b))
            elif (a in DECIDED) != (b in DECIDED):
                movers.append((div, f, a, b))
        want = "?" if expected is None else str(expected)
        flag = ""
        if expected is not None and rows != expected:
            flag = "  <-- COVERAGE SHORT"
            bad_coverage += 1
        print(f"{div:<18} {want:>5} {rows:>6} {a_dec:>7} {b_dec:>7} {errors:>10}{flag}")

    movers.sort()
    Path(args.movers_out).write_text(
        "".join(f"{f}\n" for _d, f, _a, _b in movers), encoding="utf-8"
    )
    gains = sum(1 for _d, _f, a, b in movers if a not in DECIDED and b in DECIDED)
    print()
    print(f"raw movers: {len(movers)}  ({gains} raw gains, {len(movers) - gains} raw losses)")
    print(f"  -> {args.movers_out}  (re-check every one of them 3x per arm)")
    for div, f, a, b in movers:
        direction = "GAIN" if a not in DECIDED else "LOSS"
        print(f"  {direction} [{div}] A={a:<8} B={b:<8} {os.path.basename(f)}")

    print()
    print(f"DISAGREEMENTS (one arm sat, the other unsat): {len(disagreements)}")
    for div, f, a, b in disagreements:
        print(f"  [{div}] A={a} B={b} {f}")

    if disagreements:
        print("\nA disagreement is not ambient noise: same binary, same file.", file=sys.stderr)
        return 2
    if bad_coverage:
        print("\nA short sweep measures the subset that survived.", file=sys.stderr)
        return 3
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
