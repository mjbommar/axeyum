#!/usr/bin/env python3
"""LEMMA-INPUT -- R7: the NOISE FLOOR, from one arm repeated.

Reads a multi-pass A/B TSV and reports, for ONE arm only, the spread of each
row's wall time across passes.  That band is what any arm/base ratio has to be
read against: a lane that quotes a 1.4x speedup inside a 1.5x same-arm band has
measured the machine.

Assume the band is not zero until it is measured (the pre-registration says so
in advance).  Exit non-zero if the file holds fewer than two passes, because a
one-pass file cannot produce a floor and a printed 1.000 would be a lie.
"""

import pathlib
import statistics
import sys
from collections import defaultdict

SRC = pathlib.Path(sys.argv[1])
ARM = sys.argv[2] if len(sys.argv) > 2 else "base"

walls = defaultdict(dict)
for line in SRC.read_text().splitlines():
    if not line.strip():
        continue
    p = line.split("\t")
    if len(p) != 7 or p[2] != ARM:
        continue
    walls[p[1]][p[0]] = int(p[5])

passes = sorted({pn for row in walls.values() for pn in row})
if len(passes) < 2:
    print(f"ABORT: {SRC} holds {len(passes)} pass(es) of arm '{ARM}' -- "
          "a noise floor needs at least two.")
    sys.exit(2)

spreads = []
for name, row in walls.items():
    vals = [row[pn] for pn in passes if pn in row]
    if len(vals) < 2 or min(vals) <= 0:
        continue
    spreads.append((max(vals) / min(vals), name, vals))

if not spreads:
    print("ABORT: no row has two comparable readings.")
    sys.exit(2)

spreads.sort()
vals = [s[0] for s in spreads]
print(f"noise floor, arm '{ARM}', {len(passes)} passes over {len(spreads)} rows")
print(f"  max/min per row: median {statistics.median(vals):.3f}  "
      f"p90 {vals[min(len(vals)-1, 9*len(vals)//10)]:.3f}  max {vals[-1]:.3f}")
print("  five widest rows:")
for ratio, name, v in spreads[-5:][::-1]:
    print(f"    {ratio:.3f}\t{v}\t{name}")
print()
print(f"READ ANY arm/base RATIO AGAINST THIS: a difference inside "
      f"[1/{vals[-1]:.3f}, {vals[-1]:.3f}] is not distinguishable from the "
      f"machine on this population.")
