#!/usr/bin/env python3
"""Split the A/B's moved give-up details into the ones this change CAUSED and
the ones it did not.

The detail channel moving is what proves the two arms are different binaries
(PREREGISTRATION.md R2), but "it moved" is not the same claim as "it moved
because of this change": the board's outer harness can report a `Watchdog` on
one run and a `Timeout` on the next for the same file, and that jitter also
moves the string. So the movement is attributed rather than counted.

The one number that carries the whole result is the third block: how many rows
still carry the OLD sentence in the ARM. It must be zero.

Usage: attribute-detail-moves.py <ab.tsv>...
"""

import collections
import math
import pathlib
import sys

OLD = "Fourier–Motzkin elimination exceeded the wall-clock / size budget"
NEW = [
    "lra: the deadline passed building",
    "lra: the deadline passed while linearizing",
    "lra: the deadline had already passed",
    "lra: both engines declined",
    "lra: an i128 overflow while linearizing",
]


def wilson(k, n, z=1.96):
    if n == 0:
        return None
    p = k / n
    d = 1 + z * z / n
    centre = (p + z * z / (2 * n)) / d
    half = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return max(0.0, centre - half), min(1.0, centre + half)


def kind(s):
    if s == "none":
        return "none"
    if "kind=" in s:
        return s.split("kind=")[1].split(" ")[0]
    return "?"


def main(paths):
    rows = []
    for p in paths:
        lines = pathlib.Path(p).read_text().splitlines()
        cols = lines[0].split("\t")
        rows += [dict(zip(cols, l.split("\t"))) for l in lines[1:]]
    n = len(rows)

    moved = [r for r in rows if r["base_giveup"] != r["arm_giveup"]]
    attributable = [
        r
        for r in moved
        if OLD in r["base_giveup"] and any(s in r["arm_giveup"] for s in NEW)
    ]
    other = [r for r in moved if r not in attributable]
    base_old = [r for r in rows if OLD in r["base_giveup"]]
    arm_old = [r for r in rows if OLD in r["arm_giveup"]]
    arm_new = [r for r in rows if any(s in r["arm_giveup"] for s in NEW)]

    print(f"rows: {n}")
    print(f"detail channel moved                            {len(moved)}/{n}")
    print(f"  ATTRIBUTABLE (the old lra sentence -> a new)  {len(attributable)}")
    print(f"  other (the OUTER route or kind differs)       {len(other)}")
    print()
    print(f"BASE carries the old lra sentence               {len(base_old)}/{n}")
    print(f"ARM  carries the old lra sentence               {len(arm_old)}/{n}   <- must be 0")
    print(f"ARM  carries one of the new sentences           {len(arm_new)}/{n}")
    print()
    print("which gate the ARM names, on rows the BASE called a Fourier-Motzkin timeout:")
    counts = collections.Counter()
    for r in arm_new:
        for s in NEW:
            if s in r["arm_giveup"]:
                counts[s] += 1
    for s, c in counts.most_common():
        print(f"  {c:3d}  {s}")
    print()
    print("the 'other' rows, base give-up kind -> arm give-up kind:")
    for k, c in collections.Counter(
        (kind(r["base_giveup"]), kind(r["arm_giveup"])) for r in other
    ).most_common():
        print(f"  {c:3d}  {k[0]} -> {k[1]}")

    if arm_old:
        print()
        print("FAIL: the arm still renders the sentence this change removes:")
        for r in arm_old:
            print(f"  {r['file']}")
        return 3
    if not attributable:
        print()
        print("VACUOUS: no row moved from the old sentence to a new one.")
        return 4
    lo, hi = wilson(len(arm_old), n)
    print()
    print(f"OK: 0/{n} rows still carry the old sentence, Wilson 95% [{lo:.5f}, {hi:.5f}]")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
