#!/usr/bin/env python3
"""LEMMA-INPUT -- read every claimed ratio against the SAME-ARM band of the very
row it is claimed on, not against the population's band.

The population noise floor is dominated by short rows, where a cold first pass
against two warm ones gives a 6.4x max/min on a 107 ms row.  Quoting that band
against a 25-second budget-bound row would throw away a real result; quoting a
0.55 on a row whose own base arm swings 2x would manufacture one.  So this
prints, per row, both.

Also prints the SLOWDOWNS, which a "ten largest speedups" table hides by
construction.
"""

import pathlib
import statistics
import sys
from collections import defaultdict

SRC = pathlib.Path(sys.argv[1])
WATCH = set()
if len(sys.argv) > 2:
    WATCH = {ln.strip() for ln in pathlib.Path(sys.argv[2]).read_text().splitlines() if ln.strip()}

walls = defaultdict(lambda: defaultdict(list))
for line in SRC.read_text().splitlines():
    if not line.strip():
        continue
    p = line.split("\t")
    if len(p) != 7:
        continue
    walls[p[1]][p[2]].append(int(p[5]))

rows = []
for name, arms in walls.items():
    b, a = arms.get("base", []), arms.get("arm", [])
    if not b or not a:
        continue
    bm, am = statistics.median(b), statistics.median(a)
    band = max(b) / min(b) if min(b) > 0 else float("inf")
    rows.append((am / bm if bm else float("inf"), band, name, b, a))

rows.sort()
print(f"{'ratio':>7} {'base band':>10}  row")
if WATCH:
    print("-- the rows the profile named --")
    for ratio, band, name, b, a in rows:
        if name in WATCH:
            print(f"{ratio:7.3f} {band:10.3f}  {name}\n{'':19}base={b} arm={a}")
print("-- the five largest SLOWDOWNS (the half a speedup table hides) --")
for ratio, band, name, b, a in rows[-5:][::-1]:
    print(f"{ratio:7.3f} {band:10.3f}  {name}\n{'':19}base={b} arm={a}")

outside = [r for r in rows if r[0] > r[1] or r[0] < 1 / r[1]]
print()
print(f"rows whose arm/base ratio falls OUTSIDE their own base arm's "
      f"max/min band: {len(outside)} of {len(rows)}")
for ratio, band, name, b, a in sorted(outside)[:12]:
    print(f"  {ratio:.3f} vs band {band:.3f}\t{name}")
