#!/usr/bin/env python3
"""What the SHIPPED default actually does, per division.

`shipped` is the built binary with nothing set; `preadr` is that same binary
with `AXEYUM_UFBV_MAX_SCALAR_THEORY_ATOMS=1024`, which restores the value the
tree had before ADR-1945. So this is a diff of the decision itself, measured on
one binary, rather than a comparison of two builds.

The array divisions are the point of including them: the array path's cap was
NOT changed, so `shipped` and `preadr` must be identical there. A difference is
a finding, not noise, and this prints every one.
"""
import collections
import re
import sys

rows = []
for shard in range(64):
    try:
        fh = open(f"{sys.argv[1]}/shard{shard}.tsv")
    except FileNotFoundError:
        continue
    with fh:
        h = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            q = line.rstrip("\n").split("\t")
            if len(q) == len(h):
                rows.append(dict(zip(h, q)))
if not rows:
    print("ABORT: no rows")
    sys.exit(2)
if any(r["lever_refused"] == "yes" for r in rows):
    print("ABORT: a lever refused its value on some row")
    sys.exit(2)
by = collections.defaultdict(dict)
for r in rows:
    by[r["file"]][r["arm"]] = r
arms = sorted({r["arm"] for r in rows})
if arms != ["preadr", "shipped"]:
    print(f"ABORT: arms {arms}, expected ['preadr', 'shipped']")
    sys.exit(2)
complete = sorted(f for f, d in by.items() if len(d) == 2)
partial = len(by) - len(complete)
expect = int(sys.argv[2]) if len(sys.argv) > 2 else None
if expect is not None and len(complete) != expect:
    print(f"ABORT: {len(complete)} complete files ({partial} partial), expected {expect}")
    sys.exit(2)
D = {"sat", "unsat"}


def div(f):
    m = re.search(r"(QF_[A-Z0-9]+)/", f)
    return m.group(1) if m else "?"


conflict = [
    f for f in complete
    if len({by[f][a]["verdict"] for a in arms} & D) > 1
]
if conflict:
    print(f"ABORT: {len(conflict)} file(s) where the two arms DISAGREE sat/unsat")
    for c in conflict:
        print("   ", c, {a: by[c][a]["verdict"] for a in arms})
    sys.exit(2)

print(f"# {len(complete)} files x 2 arms; 0 sat/unsat disagreements")
print()
print(f"{'division':<10} {'files':>6} {'preadr':>8} {'shipped':>8} {'gain':>5} {'loss':>5} "
      f"{'pre wall':>9} {'ship wall':>10}")
tot = collections.Counter()
for d in sorted({div(f) for f in complete}):
    fs = [f for f in complete if div(f) == d]
    pre = {f for f in fs if by[f]["preadr"]["verdict"] in D}
    shp = {f for f in fs if by[f]["shipped"]["verdict"] in D}
    pw = sum(int(by[f]["preadr"]["wall_ms"]) for f in fs) / 1000
    sw = sum(int(by[f]["shipped"]["wall_ms"]) for f in fs) / 1000
    tot["gain"] += len(shp - pre)
    tot["loss"] += len(pre - shp)
    print(f"{d:<10} {len(fs):>6} {len(pre):>8} {len(shp):>8} {len(shp - pre):>5} "
          f"{len(pre - shp):>5} {pw:>9.1f} {sw:>10.1f}")
print(f"{'TOTAL':<10} {len(complete):>6} {'':>8} {'':>8} {tot['gain']:>5} {tot['loss']:>5}")
print()
for d in sorted({div(f) for f in complete}):
    fs = [f for f in complete if div(f) == d]
    pre = {f for f in fs if by[f]["preadr"]["verdict"] in D}
    shp = {f for f in fs if by[f]["shipped"]["verdict"] in D}
    for f in sorted(pre - shp):
        print(f"LOSS  {d}  {f}")
        print(f"      preadr {by[f]['preadr']['verdict']} in "
              f"{int(by[f]['preadr']['wall_ms']) / 1000:.1f}s; shipped "
              f"{by[f]['shipped']['verdict']} in "
              f"{int(by[f]['shipped']['wall_ms']) / 1000:.1f}s")
        print(f"      {by[f]['shipped']['giveup'][:140]}")
# The array divisions must be untouched: the array path's cap did not move.
for d in ("QF_ABV", "QF_ABVFP"):
    fs = [f for f in complete if div(f) == d]
    if not fs:
        continue
    differ = [f for f in fs if by[f]["preadr"]["verdict"] != by[f]["shipped"]["verdict"]]
    print(f"{d}: {len(differ)} of {len(fs)} files differ in VERDICT between the arms "
          f"(expected 0 -- the array path's cap is unchanged)")
    for f in differ:
        print(f"   {f}: preadr {by[f]['preadr']['verdict']} vs "
              f"shipped {by[f]['shipped']['verdict']}")
