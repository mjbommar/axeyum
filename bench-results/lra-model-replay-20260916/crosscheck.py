#!/usr/bin/env python3
"""Cross-check this lane's target population against LRA-TRACE's independent
measurement of the same wall (`bench-results/lra-trace-20260915/buckets-93.tsv`,
whose `modelprobe` column was captured at the SHIPPED atom screen).

Usage: crosscheck.py <per-file.tsv> <undecided-93.txt> <buckets-93.tsv>
"""

import collections
import csv
import sys

rows = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
tgt = {r["file"] for r in rows if r["last_arm"] in ("no-model", "no-replay")}
u93 = {l.strip() for l in open(sys.argv[2]) if l.strip()}
print(f"target population:                                      {len(tgt)}")
print(f"of which in LRA-TRACE's 93 undecided:                    {len(tgt & u93)}")
print(f"of which NOT in the 93 (decided at the shipped screen):  {len(tgt - u93)}")
for f in sorted(tgt - u93):
    print(f"    outside-93: {f}")

b = {r["file"]: r["modelprobe"] for r in csv.DictReader(open(sys.argv[3]), delimiter="\t")}
print()
print("LRA-TRACE's own modelprobe column, restricted to our target n 93:")
c = collections.Counter(b.get(f, "(not in that table)") for f in sorted(tgt & u93))
for k, v in sorted(c.items(), key=lambda kv: -kv[1]):
    print(f"  {v:4d}  {k}")
