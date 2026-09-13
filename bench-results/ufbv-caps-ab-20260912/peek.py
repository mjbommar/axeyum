#!/usr/bin/env python3
"""Partial read of an in-flight sweep: only files whose whole arm row is done.

NOT the reported result -- `summarize.py` is, and it aborts on an incomplete
matrix on purpose. This exists so a long sweep can be watched, and it prints its
own denominator so a partial number cannot be quoted as a final one.
"""
import collections
import glob
import re
import sys

outdir = sys.argv[1]
rows = []
for p in glob.glob(f"{outdir}/shard*.tsv"):
    with open(p) as fh:
        h = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if len(parts) == len(h):
                rows.append(dict(zip(h, parts)))

by = collections.defaultdict(dict)
for r in rows:
    by[r["file"]][r["arm"]] = r
arms = sorted({r["arm"] for r in rows})
complete = [f for f, d in by.items() if len(d) == len(arms)]
print(f"PARTIAL -- arms={arms}")
print(f"PARTIAL -- complete files so far: {len(complete)} (not the denominator)")
D = {"sat", "unsat"}
base = {f for f in complete if by[f]["base"]["verdict"] in D}
print(f"baseline decides {len(base)} of {len(complete)}")
for a in arms:
    dec = {f for f in complete if by[f][a]["verdict"] in D}
    wall = sum(int(by[f][a]["wall_ms"]) for f in complete) / 1000.0
    print(
        f"{a:<9} decided={len(dec):3d} gain={len(dec - base):2d} "
        f"loss={len(base - dec):2d} wall={wall:7.1f}s"
    )
und = [f for f in complete if f not in base]
print(f"\n-- give-up on baseline-undecided (n={len(und)}) --")
for a in arms:
    c = collections.Counter()
    for f in und:
        r = by[f][a]
        if r["verdict"] in D:
            c["DECIDED"] += 1
            continue
        c[re.sub(r"\d+", "N", r["giveup"])[:100]] += 1
    print(f"-- {a}")
    for k, v in c.most_common(5):
        print(f"   {v:3d} {k}")
