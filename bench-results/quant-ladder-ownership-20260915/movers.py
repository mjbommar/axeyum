#!/usr/bin/env python3
"""Every row that MOVED in the ADR-2103 A/B, as absolute corpus paths.

A row moved if its VERDICT differs between the arms **or** its EXIT STATUS does.
Both, because ADR-2045 measured `losses=0` by verdict with five new ABORTS
underneath it: a run that keeps every verdict and changes how the process ended
has changed something the verdict column cannot see, and a recheck that only
re-runs verdict movers would never look at it.

The output feeds `launch-recheck.sh`, which runs ADR-2100's own
`recheck-movers.sh` three times per arm. ADR-1966 reported 25 raw movers and 22
after re-checking -- **11 of its 18 movers outside the treatment division
vanished** -- so the raw column overstates in both directions and the classified
one is the only one an exit criterion may be read off.

Usage: movers.py <tsv>...          # writes paths to stdout
"""

import sys

CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"


def main():
    moved = []
    malformed = 0
    seen = 0
    for path in sys.argv[1:]:
        for line in open(path):
            cells = line.rstrip("\n").split("\t")
            if cells[0] == "file":
                continue
            if len(cells) != 9:
                # Counted and reported, never silently dropped: reading a parse
                # failure as "no movement" is how a measurement manufactures a
                # null (ADR-1966 excluded 39 such rows by name).
                malformed += 1
                continue
            seen += 1
            f, a, _a_ms, a_rc, b, _b_ms, b_rc, _first, _status = cells
            if a != b or a_rc != b_rc:
                moved.append(f)
    for f in sorted(set(moved)):
        print(CORPUS + f)
    print(
        f"rows={seen} movers={len(set(moved))} malformed={malformed}",
        file=sys.stderr,
    )
    if malformed:
        sys.exit(f"ABORT: {malformed} malformed rows -- fix the capture, do not score around it")


if __name__ == "__main__":
    main()
