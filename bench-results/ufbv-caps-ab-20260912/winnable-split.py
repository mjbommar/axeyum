#!/usr/bin/env python3
"""Split each arm's gains into the WINNABLE 87 and the rest.

The winnable set is the census denominator: files we leave `unknown` while a
reference decides. A gain outside it is still a gain, but it is not a gap the
census sized, and reporting the two together would inflate the answer to the
question the census asked.
"""
import collections
import glob
import sys

outdir, winnable_list, corpus = sys.argv[1], sys.argv[2], sys.argv[3]
win = {l.strip().replace(corpus, "") for l in open(winnable_list) if l.strip()}
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
files = set(by)
print(f"winnable list has {len(win)}; {len(win & files)} of them are in the swept population")
missing = win - files
if missing:
    print(f"ABORT: {len(missing)} winnable files are not in the sweep")
    for m in sorted(missing)[:5]:
        print("   ", m)
    sys.exit(2)
base = {f for f in files if by[f]["base"]["verdict"] in D}
if base & win:
    print(f"ABORT: {len(base & win)} winnable files are DECIDED by the baseline -- "
          "the winnable set is stale against this sweep")
    sys.exit(2)
print(f"baseline decides {len(base)}; leaves {len(files - base)} undecided, "
      f"of which {len(win)} are winnable and {len(files - base - win)} are not")
print()
print(f"{'arm':<10} {'gain':>5} {'of the 87':>10} {'outside':>8}")
for a in sorted({r["arm"] for r in rows}):
    g = {f for f in files if by[f][a]["verdict"] in D} - base
    print(f"{a:<10} {len(g):>5} {len(g & win):>10} {len(g - win):>8}")
print()
print("verdict split of the best arm's gains, and how close each ran to the 24 s budget:")
best = max(
    (a for a in {r["arm"] for r in rows}),
    key=lambda a: len({f for f in files if by[f][a]["verdict"] in D}),
)
g = sorted({f for f in files if by[f][best]["verdict"] in D} - base)
sat = sum(1 for f in g if by[f][best]["verdict"] == "sat")
print(f"  arm {best}: {len(g)} gains, {sat} sat / {len(g) - sat} unsat")
buckets = collections.Counter()
for f in g:
    ms = int(by[f][best]["wall_ms"])
    buckets["<5s" if ms < 5000 else "5-10s" if ms < 10000 else
            "10-15s" if ms < 15000 else "15-20s" if ms < 20000 else ">=20s"] += 1
for k in ("<5s", "5-10s", "10-15s", "15-20s", ">=20s"):
    print(f"    {k:<7} {buckets[k]}")
