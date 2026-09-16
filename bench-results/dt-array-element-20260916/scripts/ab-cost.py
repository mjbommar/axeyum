#!/usr/bin/env python3
"""DT-ARRAY-ELEMENT -- the COST side of the interleaved A/B.

    ab-cost.py <division> <ab-*.shard*.tsv ...>

`ab-summarize.py` answers "did a verdict move". This answers "what did the arm
spend", which is the other half of a ship decision and the half a null A/B
still has something to say about: a lever with 0 gains that also costs time is
strictly worse than OFF, and saying so needs a number.

The arms are interleaved per file on one core, so the per-file DIFFERENCE is
the only quantity here that load does not dominate. Totals are reported too,
but the per-file medians and the worst regressions are what to read.
"""

import os
import statistics
import sys


def main():
    if len(sys.argv) < 3:
        sys.stderr.write(__doc__)
        return 2
    div, paths = sys.argv[1], sys.argv[2:]
    deltas = []
    base_total = arm_total = 0
    rows = 0
    for path in paths:
        with open(path) as fh:
            next(fh, None)
            for line in fh:
                parts = line.rstrip("\n").split("\t")
                if len(parts) < 6:
                    continue
                name, _b, b_ms, _a, a_ms, _first = parts[:6]
                try:
                    b_ms, a_ms = int(b_ms), int(a_ms)
                except ValueError:
                    continue
                rows += 1
                base_total += b_ms
                arm_total += a_ms
                deltas.append((a_ms - b_ms, os.path.basename(name), b_ms, a_ms))
    if not rows:
        sys.stderr.write("no rows parsed -- refusing to report a cost from nothing\n")
        return 2
    # THE GUARD THAT SHOULD HAVE EXISTED THE FIRST TIME. On s7 (uutils
    # coreutils 0.8.0) `date +%s%3N` prints NANOSECONDS, so the column is not
    # milliseconds and its differences are not even consistently positive --
    # this script's first run over the 2026-09-16 captures reported a total of
    # -20,454,778,950,164,076,537 ms and printed it as a finding. A per-file
    # elapsed outside [0, 10x the budget] cannot be a wall time at a 24 s
    # budget, so refuse the whole file rather than report a number from it.
    ceiling = 10 * 24_000
    bad = [x for x in deltas if abs(x[2]) > ceiling or abs(x[3]) > ceiling
           or x[2] < 0 or x[3] < 0]
    if bad:
        sys.stderr.write(
            f"REFUSING: {len(bad)} of {rows} rows carry an elapsed outside "
            f"[0, {ceiling}] ms, so the column is not a millisecond wall time. "
            f"First: {bad[0][1]} base={bad[0][2]} arm={bad[0][3]}. See "
            "scripts/ab-run.sh's note on `date +%s%3N` under uutils coreutils.\n"
        )
        return 3
    deltas.sort()
    d = [x[0] for x in deltas]
    print(f"### {div}: {rows} rows")
    print(f"  total base {base_total} ms / arm {arm_total} ms "
          f"({arm_total - base_total:+d} ms, {100.0 * (arm_total - base_total) / max(base_total, 1):+.1f}%)")
    print(f"  per-file delta (arm - base): median {statistics.median(d):+.0f} ms, "
          f"mean {statistics.mean(d):+.1f} ms")
    print(f"  rows where the arm is SLOWER by >1000 ms: {sum(1 for x in d if x > 1000)}")
    print(f"  rows where the arm is FASTER by >1000 ms: {sum(1 for x in d if x < -1000)}")
    for label, sl in (("worst 3 regressions", deltas[-3:][::-1]), ("best 3 speedups", deltas[:3])):
        print(f"  {label}:")
        for delta, name, b_ms, a_ms in sl:
            print(f"    {delta:+8d} ms  base={b_ms:6d} arm={a_ms:6d}  {name}")
    print()
    return 0


raise SystemExit(main())
