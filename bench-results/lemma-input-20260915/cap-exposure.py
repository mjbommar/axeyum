#!/usr/bin/env python3
"""LEMMA-INPUT -- R17: how much of the DECIDED half an input cap would bite.

A cap that only makes undecided rows finish sooner costs nothing.  The cost is
on rows that are exiting cleanly today, so this reports the exposure there
separately -- and separately again for the rows whose reading is missing, which
are counted as UNKNOWN EXPOSURE rather than as zero.
"""

import math
import pathlib
import sys

ATTR = pathlib.Path(sys.argv[1])
DECIDED = pathlib.Path(sys.argv[2])
CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 512

decided = {ln.strip() for ln in DECIDED.read_text().splitlines() if ln.strip()}


def wilson(k, n, z=1.96):
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = p + z * z / (2 * n)
    r = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    return ((c - r) / d, (c + r) / d)


read = cross = noread = 0
crossers = []
for line in ATTR.read_text().splitlines():
    if not line.strip():
        continue
    p = line.split("\t")
    if p[0] not in decided:
        continue
    if p[4].strip() == "NOREAD":
        noread += 1
        continue
    read += 1
    fields = {}
    for tok in p[4].split():
        if "=" in tok:
            k, v = tok.split("=", 1)
            if v.lstrip("-").isdigit():
                fields[k] = int(v)
    if fields.get("max_atoms", 0) > CAP:
        cross += 1
        crossers.append((fields["max_atoms"], p[0], p[1]))

print(f"decided (control) rows: {len(decided)}")
print(f"  with a reading:                 {read}")
print(f"  NOREAD -- exposure UNKNOWN:     {noread}")
print(f"  reading and crossing {CAP} atoms: {cross}")
lo, hi = wilson(cross, read)
print(f"  Wilson 95 % on {cross}/{read}: [{lo:.1%}, {hi:.1%}]")
print()
for atoms, name, verdict in sorted(crossers, reverse=True):
    print(f"  max_atoms={atoms}\t{verdict}\t{name}")
if cross == 0:
    print()
    print("FINDING: no decided row crosses the cap, so enforcing it is free HERE.")
