#!/usr/bin/env python3
"""UFLIA-TRACE -- why is a silent universal silent?

Reads one run's `AXEYUM_QPROBE` stream on stdin and splits the universals that
admitted NOTHING into the two classes that have OPPOSITE remedies:

  NO-TRIGGER      `patterns=0`             no trigger at all; nothing can fire
  NEVER-MATCHED   `patterns>0, joined=0`   a trigger exists and the e-graph
                                           never produced a tuple for it --
                                           reachable by proposing a DIFFERENT
                                           trigger, and by nothing else
  ALL-REJECTED    `joined>0, admitted=0`   tuples were found and none became an
                                           instance -- reachable by changing the
                                           admission path, and NOT by proposing
                                           more triggers

Lumping the last two together is how a lane sizes a trigger lever off rows a
trigger lever cannot move. The dominant reason is printed per class from the
`rej_*` fields, verbatim, because a bucket sized by its LABEL reports one cause
where the raw fields hold thirteen.

**`AXEYUM_QPROBE_CENSUS=1` IS REQUIRED for those reasons to exist at all.**
`AdmissionCensus::enabled` is `qprobe_enabled() && census_enabled()`, so under
plain `AXEYUM_QPROBE=1` every `rej_*` field prints `0` -- including on
universals that admitted hundreds of instances, whose `census_admitted` is also
`0`. An all-zero reject vector beside a nonzero `joined` is therefore the
signature of an instrument that was OFF, and reading it as "rejected for no
recorded reason" attributes a cause to a measurement nobody took. This script
detects that shape and says `REASONS-UNMEASURED` instead of printing zeros.

Prints one summary block; `--rows` adds one line per silent universal.
"""

from __future__ import annotations

import collections
import re
import sys

# `re.M` is load-bearing: without it `$` anchors to the end of the WHOLE input,
# so this pattern matched at most the last line of a run and every file came
# back `NO-PROBE-ROWS` -- an empty result from an instrument that was pointed at
# the subject and could not see it, which reads exactly like a strong negative.
UNIVERSAL = re.compile(
    r"QPROBE\s+universal\[(\d+)\] vars=(\d+) patterns=(\d+) joined=(\d+) "
    r"starved_joins=(\d+) admitted=(\d+) (.*)$",
    re.M,
)
REJ = re.compile(r"(rej_\w+)=(\d+)")


def main() -> None:
    text = sys.stdin.read()
    rows = []
    last = -1
    segments: list[list] = []
    current: list = []
    for m in UNIVERSAL.finditer(text):
        idx = int(m.group(1))
        if idx <= last and current:
            segments.append(current)
            current = []
        last = idx
        current.append(m)
    if current:
        segments.append(current)
    if not segments:
        # NOT "no universal was silent": this run exited before the probe block,
        # which sits behind `if admitted.is_empty()`.
        print("NO-PROBE-ROWS")
        return
    widest = max(segments, key=len)

    counts: collections.Counter[str] = collections.Counter()
    rejects: dict[str, collections.Counter[str]] = collections.defaultdict(
        collections.Counter
    )
    # Whether the admission census ran at all, decided from the data rather than
    # from the environment this script cannot see: any nonzero `rej_*` or
    # `census_admitted` anywhere proves it did.
    census_ran = False
    for m in widest:
        tail = m.group(7)
        if any(int(v) > 0 for _, v in REJ.findall(tail)) or any(
            int(v) > 0 for v in re.findall(r"census_admitted=(\d+)", tail)
        ):
            census_ran = True
    for m in widest:
        patterns, joined, admitted = int(m.group(3)), int(m.group(4)), int(m.group(6))
        if admitted > 0:
            counts["FIRED"] += 1
            continue
        if patterns == 0:
            cls = "NO-TRIGGER"
        elif joined == 0:
            cls = "NEVER-MATCHED"
        else:
            cls = "ALL-REJECTED"
        counts[cls] += 1
        for name, value in REJ.findall(m.group(7)):
            if int(value) > 0:
                rejects[cls][name] += int(value)
        rows.append((cls, m.group(1), patterns, joined, admitted))

    total = sum(counts.values())
    print(f"universals {total}")
    for cls in ("FIRED", "NO-TRIGGER", "NEVER-MATCHED", "ALL-REJECTED"):
        n = counts[cls]
        print(f"  {cls:15s} {n:5d}  {100 * n / total:5.1f}%")
    if not census_ran:
        print(
            "  REASONS-UNMEASURED  every rej_* and census_admitted is 0, which is "
            "what AdmissionCensus prints when it is OFF -- re-run with "
            "AXEYUM_QPROBE_CENSUS=1"
        )
    else:
        for cls, counter in sorted(rejects.items()):
            top = ", ".join(f"{k}={v}" for k, v in counter.most_common(6))
            print(f"  rejects[{cls}] {top}")
    if "--rows" in sys.argv:
        for row in rows:
            print("ROW\t" + "\t".join(str(x) for x in row))


if __name__ == "__main__":
    main()
