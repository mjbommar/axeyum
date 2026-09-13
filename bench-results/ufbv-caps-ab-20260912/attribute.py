#!/usr/bin/env python3
"""Attribute each gain to the cap that actually produced it.

A gain counted against `base` alone cannot say WHICH cap bought it, because the
two caps are sequential gates: a file blocked at the node cap never reaches the
atom check, so raising the node cap can move a file's give-up reason without
deciding it. The set differences below are what separate the two.
"""
import collections
import glob
import sys

outdir = sys.argv[1]
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
arms = sorted({r["arm"] for r in rows})
D = {"sat", "unsat"}


def dec(a):
    return {f for f, d in by.items() if a in d and d[a]["verdict"] in D}


base = dec("base")
print(f"files={len(by)} arms={arms}")
print(f"base decides {len(base)}")
for a in arms:
    if a == "base":
        continue
    print(f"  {a:<9} decided={len(dec(a)):3d}  +{len(dec(a) - base):<3d} -{len(base - dec(a))}")


def diff(x, y, label):
    s = sorted(dec(x) - dec(y))
    print(f"\n{label}  ({len(s)})")
    for f in s:
        print(f"   {by[f][x]['verdict']:<6} {int(by[f][x]['wall_ms']) / 1000:>6.1f}s  {f}")
        print(f"          base gave up: {by[f]['base']['giveup'][:110]}")


if "bothmid" in arms and "a4096" in arms:
    diff("bothmid", "a4096", "bought by the NODE cap on top of atoms=4096")
if "bothmax" in arms and "bothmid" in arms:
    diff("bothmax", "bothmid", "bought by going 4096/65536 -> 8192/262144")
if "a8192" in arms and "a4096" in arms:
    diff("a8192", "a4096", "bought by atoms 4096 -> 8192")
if "a4096" in arms and "a2048" in arms:
    diff("a4096", "a2048", "bought by atoms 2048 -> 4096")

print("\nwall totals over the whole population (s):")
for a in arms:
    w = sum(int(by[f][a]["wall_ms"]) for f in by if a in by[f]) / 1000
    print(f"  {a:<9} {w:8.1f}   x{w / (sum(int(by[f]['base']['wall_ms']) for f in by) / 1000):.2f}")
