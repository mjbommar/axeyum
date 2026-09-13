#!/usr/bin/env python3
"""Emit the absolute paths of every file ANY arm newly decides.

The union, not one arm's set: a file a single arm converts is a claim this lane
makes and has to stand up to both references, whether or not the arm that
converted it is the one recommended.
"""
import collections
import glob
import sys

outdir, corpus = sys.argv[1], sys.argv[2]
rows = []
for p in glob.glob(f"{outdir}/shard*.tsv"):
    with open(p) as fh:
        h = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            q = line.rstrip("\n").split("\t")
            if len(q) == len(h):
                rows.append(dict(zip(h, q)))
by = collections.defaultdict(dict)
for r in rows:
    by[r["file"]][r["arm"]] = r
D = {"sat", "unsat"}
base = {f for f, d in by.items() if d["base"]["verdict"] in D}
gained = set()
for a in {r["arm"] for r in rows}:
    gained |= {f for f, d in by.items() if d[a]["verdict"] in D} - base
for f in sorted(gained):
    print(corpus + f)
print(f"# {len(gained)} files", file=sys.stderr)
