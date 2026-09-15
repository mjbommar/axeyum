#!/usr/bin/env python3
"""Every row whose DECIDEDNESS moved between the two arms, as a file list.

A mover is a row where exactly one arm returned `sat` or `unsat`.  Both
directions go in one list on purpose: the re-check classifies them, and a list
that only carried the losses would make the gains unverifiable by the same
method -- which is how a re-check stops being symmetric.

A single interleaved pairing at 24 s carries a measured 1-1.5 % ambient flip
rate on these boxes, so a raw mover is a candidate and not a finding.
ADR-1966 reported 25 raw movers and 22 after re-checking, with 11 of its 18
movers outside the treatment division vanishing entirely.

Usage:
    python3 movers.py --out LIST <tsv>...
"""

from __future__ import annotations

import argparse
from pathlib import Path

CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
DECIDED = {"sat", "unsat"}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", required=True)
    ap.add_argument("tsv", nargs="+")
    args = ap.parse_args()

    movers: list[tuple[str, str, str]] = []
    malformed = 0
    for path in args.tsv:
        for line in Path(path).read_text(encoding="utf-8").splitlines():
            cells = line.split("\t")
            if cells and cells[0] == "file":
                continue
            if len(cells) != 9:
                malformed += 1
                continue
            a, b = cells[1], cells[4]
            if (a in DECIDED) != (b in DECIDED):
                movers.append((cells[0], a, b))

    movers.sort()
    Path(args.out).write_text(
        "".join(f"{CORPUS}{path}\n" for path, _a, _b in movers), encoding="utf-8"
    )
    gains = sum(1 for _p, a, b in movers if a not in DECIDED and b in DECIDED)
    losses = len(movers) - gains
    print(f"{len(movers)} movers ({gains} raw gains, {losses} raw losses) -> {args.out}")
    print(f"malformed rows skipped: {malformed}")
    for path, a, b in movers:
        direction = "GAIN" if a not in DECIDED else "LOSS"
        print(f"  {direction} A={a:<8} B={b:<8} {path}")

    # Exit status depends on the finding: no movers at all means there is
    # nothing to re-check, which a caller must not read as "re-check passed".
    return 0 if movers else 3


if __name__ == "__main__":
    raise SystemExit(main())
