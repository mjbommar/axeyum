#!/usr/bin/env python3
"""Row-level noise floor from two independent passes of the SAME arm.

The census's PLAIN arm and the A/B's BASE arm are the identical configuration
(one binary, `AXEYUM_MEMORY_LIMIT_MB` unset, 24 s, 8 GiB `ulimit -v`, the same
six pinned pairs), run about ten minutes apart with different neighbours.  Any
row whose decided/undecided status differs between them moved for no reason at
all.

COUNTS ARE NOT ENOUGH.  Both passes can read 107 while disagreeing on rows in
both directions -- ADR-2030's 21.8% was 10.2% at row level.  So this compares
ROW BY ROW and reports the identity of every row that moved.

Usage: noise-floor.py <census-tsv...> -- <ab-tsv...>
"""
import sys

DEC = ("sat", "unsat")
split = sys.argv.index("--")
cen_paths, ab_paths = sys.argv[1:split], sys.argv[split + 1:]


def load(paths, verdict_col):
    out = {}
    for p in paths:
        with open(p) as fh:
            head = fh.readline().rstrip("\n").split("\t")
            for line in fh:
                r = dict(zip(head, line.rstrip("\n").split("\t")))
                out[r["file"]] = r[verdict_col]
    return out


a = load(cen_paths, "P")      # census plain arm
b = load(ab_paths, "base")    # A/B base arm

common = sorted(set(a) & set(b))
print(f"pass A (census, plain arm): {len(a)} rows, decided={sum(1 for v in a.values() if v in DEC)}")
print(f"pass B (A/B, base arm):     {len(b)} rows, decided={sum(1 for v in b.values() if v in DEC)}")
print(f"common rows: {len(common)}")

moved = [f for f in common if (a[f] in DEC) != (b[f] in DEC)]
flipped = [f for f in common if a[f] in DEC and b[f] in DEC and a[f] != b[f]]
print(f"\nNOISE FLOOR (decided-status differs between two identical passes): "
      f"{len(moved)} of {len(common)}")
for f in moved:
    print(f"  A={a[f]:>7}  B={b[f]:>7}  {f.split('non-incremental/')[-1]}")
print(f"verdict IDENTITY flips between identical passes: {len(flipped)}")
for f in flipped:
    print(f"  A={a[f]} B={b[f]} {f}")
