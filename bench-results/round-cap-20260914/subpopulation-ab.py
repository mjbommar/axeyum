"""ADR-2035 -- the A/B restricted to the populations where the lever can fire.

The main arm's denominator is 129 files, but the lever only executes on files
that cross the boundary at `site=solve`. Reporting only the 129-file number
would hide whether the lever moved anything *where it ran*, and reporting only
the sub-population would inflate the rate. Both are printed, with their
denominators, and the sub-population is taken from the ORDERED PROBE's measured
crossings rather than from the census -- the census names 22 files and the
shipped path crosses on many more.

Usage: subpopulation-ab.py
"""

import csv
import glob
import math
import os

BASE = os.path.dirname(os.path.abspath(__file__))
DECIDED = {"sat", "unsat"}


def wilson(k, n, z=1.96):
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = p + z * z / (2 * n)
    s = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    return (max(0.0, (c - s) / d * 100), min(100.0, (c + s) / d * 100))


rows = []
for path in sorted(glob.glob(os.path.join(BASE, "ab", "main.shard*.tsv"))):
    rows += list(csv.DictReader(open(path), delimiter="\t"))

targets = {
    line.strip()
    for line in open(os.path.join(BASE, "lists", "target-22.txt"))
    if line.strip()
}

crossing_solve, crossing_any = set(), set()
for name in ("probe-off.shard0.tsv", "probe-off.shard1.tsv"):
    for r in csv.DictReader(open(os.path.join(BASE, "ab", name)), delimiter="\t"):
        if int(r["solve"]) > 0:
            crossing_solve.add(r["file"])
        if int(r["solve"]) + int(r["preflight"]) > 0:
            crossing_any.add(r["file"])

for label, sel in (
    ("ALL (the pre-registered denominator)", None),
    ("the 22 CENSUSED target files", targets),
    ("files crossing at site=solve -- where the lever can fire", crossing_solve),
    ("files crossing the boundary at EITHER site", crossing_any),
):
    sub = rows if sel is None else [r for r in rows if r["file"] in sel]
    gain = [r for r in sub if r["off_verdict"] not in DECIDED and r["on_verdict"] in DECIDED]
    loss = [r for r in sub if r["off_verdict"] in DECIDED and r["on_verdict"] not in DECIDED]
    flip = [
        r
        for r in sub
        if r["off_verdict"] in DECIDED
        and r["on_verdict"] in DECIDED
        and r["off_verdict"] != r["on_verdict"]
    ]
    n = len(sub)
    glo, ghi = wilson(len(gain), n)
    print(f"=== {label} ===")
    print(f"  rows {n}   OFF decided {sum(r['off_verdict'] in DECIDED for r in sub)}"
          f"   ON decided {sum(r['on_verdict'] in DECIDED for r in sub)}")
    print(f"  GAIN {len(gain)}  Wilson 95% [{glo:.1f}%, {ghi:.1f}%]"
          f"   LOSS {len(loss)}   FLIP {len(flip)}")
    for r in gain + loss + flip:
        print(f"    {r['off_verdict']}({r['off_ms']}ms) -> {r['on_verdict']}({r['on_ms']}ms)"
              f"  order={r['order']}  {r['file']}")
