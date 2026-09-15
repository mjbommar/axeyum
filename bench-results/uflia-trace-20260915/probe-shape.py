#!/usr/bin/env python3
"""UFLIA-TRACE -- reduce one run's `AXEYUM_QPROBE` stream to the e-matching shape.

Reads a solver run's combined output on stdin and prints ONE tab-separated row:

    universals  triggerless  rounds  joined  starved  admitted  silent

`universals`/`triggerless` come from the widest `egraph-fixpoint` line, the
per-universal sums from the `universal[i]` rows of that same build, `rounds`
from the `loop-exit` line.

`silent` is the count of universals whose `admitted=0` -- the never-instantiated
bodies. It is `NA`, never 0, when the run printed no per-universal rows: the
probe block sits behind `if admitted.is_empty()` in `qinst_egraph.rs`, so a run
that exits on a TIME budget mid-round never reaches it. Printing 0 there would
report "no universal was silent" for a run that measured no universal at all --
an empty result from an instrument never pointed at the subject, reported as a
strong negative.
"""

import re
import sys

FIXPOINT = re.compile(
    r"QPROBE egraph-fixpoint round=(\d+) ground=(\d+) foralls=(\d+) "
    r"patterns=(\d+) triggerless=(\d+)"
)
UNIVERSAL = re.compile(
    r"QPROBE\s+universal\[(\d+)\] vars=(\d+) patterns=(\d+) joined=(\d+) "
    r"starved_joins=(\d+) admitted=(\d+)"
)
LOOPEXIT = re.compile(r"QPROBE loop-exit kind=(\S+) exit=(\S+) rounds=(\d+) ground=(\d+)")


def main() -> None:
    text = sys.stdin.read()

    foralls = triggerless = 0
    for m in FIXPOINT.finditer(text):
        # A query builds the matcher several times (retry budgets, discovery
        # rebuilds). Take the WIDEST build, the same rule
        # `universals-without-triggers-2026-09-10.md` used, so a late narrow
        # rebuild cannot shrink the population.
        if int(m.group(3)) >= foralls:
            foralls = int(m.group(3))
            triggerless = int(m.group(5))

    rounds = 0
    for m in LOOPEXIT.finditer(text):
        rounds = max(rounds, int(m.group(3)))

    # Per-universal rows restart their index at each build; segment on a
    # non-increasing index and keep the largest segment.
    segments: list[dict[int, tuple[int, int, int]]] = []
    current: dict[int, tuple[int, int, int]] = {}
    last = -1
    for m in UNIVERSAL.finditer(text):
        idx = int(m.group(1))
        if idx <= last and current:
            segments.append(current)
            current = {}
        last = idx
        current[idx] = (int(m.group(4)), int(m.group(5)), int(m.group(6)))
    if current:
        segments.append(current)

    if segments:
        widest = max(segments, key=len)
        joined = sum(v[0] for v in widest.values())
        starved = sum(v[1] for v in widest.values())
        admitted = sum(v[2] for v in widest.values())
        silent = str(sum(1 for v in widest.values() if v[2] == 0))
        if not foralls:
            foralls = len(widest)
    else:
        joined = starved = admitted = 0
        silent = "NA"

    print(f"{foralls}\t{triggerless}\t{rounds}\t{joined}\t{starved}\t{admitted}\t{silent}")


if __name__ == "__main__":
    main()
