#!/usr/bin/env python3
"""Summarize a replication: per file and arm, how often it decided and how long.

Prints the FULL distribution, not a mean. A file that decides 7 times out of 9
and blows the budget twice is a different finding from one that decides every
time 2 s slower, and an average hides the difference.
"""
import collections
import statistics
import sys

rows = []
with open(sys.argv[1]) as fh:
    h = fh.readline().rstrip("\n").split("\t")
    for line in fh:
        q = line.rstrip("\n").split("\t")
        if len(q) == len(h):
            rows.append(dict(zip(h, q)))
if any(r["lever_refused"] == "yes" for r in rows):
    print("ABORT: a lever refused its value on some row")
    sys.exit(2)
D = {"sat", "unsat"}
by = collections.defaultdict(list)
for r in rows:
    by[(r["file"], r["arm"])].append(r)
files = sorted({r["file"] for r in rows})
arms = sorted({r["arm"] for r in rows})
short = {f: f.split("/")[-1][:44] for f in files}
print(f"{'file':<46} {'arm':<9} {'decided':>9} {'median s':>9} {'min':>7} {'max':>7}")
for f in files:
    for a in arms:
        rs = by[(f, a)]
        if not rs:
            continue
        dec = sum(1 for r in rs if r["verdict"] in D)
        ws = sorted(int(r["wall_ms"]) / 1000 for r in rs)
        print(
            f"{short[f]:<46} {a:<9} {dec:>4}/{len(rs):<4} "
            f"{statistics.median(ws):>9.1f} {ws[0]:>7.1f} {ws[-1]:>7.1f}"
        )
    print()
