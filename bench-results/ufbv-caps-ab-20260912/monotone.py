#!/usr/bin/env python3
"""Is the decided set monotone along each cap ladder?

If raising a cap is doing what the mechanism says, a file decided at a lower
value should still be decided at a higher one. Every exception is a file whose
verdict turned on something other than the cap -- ambient load against a 24 s
budget, most likely -- and is therefore a direct read on how noisy this sweep
is, without needing a second run.
"""
import collections
import glob
import sys

outdir = sys.argv[1]
ladders = [a.split(",") for a in sys.argv[2:]]
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


def dec(a):
    return {f for f, d in by.items() if d[a]["verdict"] in D}


total = 0
for lad in ladders:
    print(f"ladder {' -> '.join(lad)}")
    for lo, hi in zip(lad, lad[1:]):
        drop = sorted(dec(lo) - dec(hi))
        total += len(drop)
        print(f"   {lo:>8} -> {hi:<8} decided {len(dec(lo)):3d} -> {len(dec(hi)):3d}, "
              f"{len(drop)} decided at {lo} but NOT at {hi}")
        for f in drop:
            print(f"       {by[f][lo]['verdict']} in {int(by[f][lo]['wall_ms']) / 1000:.1f}s; "
                  f"at {hi}: {by[f][hi]['verdict']} in {int(by[f][hi]['wall_ms']) / 1000:.1f}s")
            print(f"         {f}")
            print(f"         {by[f][hi]['giveup'][:110]}")
print(f"\n{total} non-monotone file(s) across all ladders")
