#!/usr/bin/env python3
"""R3: which of OUR undecided rows does a reference actually decide?

A row we do not decide is a PRIZE only if some reference decides it at the same
budget.  Rows nobody decides are reported separately and never counted toward a
gap -- otherwise the "59-file gap" is sized against files that are simply hard.

Cross-tabulates the census bucket (why WE stopped) against reference agreement,
so the report can say which structural cause is actually costing board files.

Usage: addressable.py <census-rows.tsv> <ref.tsv...>
"""
import sys
from collections import Counter, defaultdict

DEC = ("sat", "unsat")
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"

cen = {}
with open(sys.argv[1]) as fh:
    head = fh.readline().rstrip("\n").split("\t")
    for line in fh:
        r = dict(zip(head, line.rstrip("\n").split("\t")))
        cen[r["file"]] = r

ref = {}
for p in sys.argv[2:]:
    with open(p) as fh:
        head = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            r = dict(zip(head, line.rstrip("\n").split("\t")))
            ref[r["file"].replace(CORPUS, "")] = r

common = sorted(set(cen) & set(ref))
print(f"census rows={len(cen)} reference rows={len(ref)} common={len(common)}")
if len(common) < len(cen):
    print(f"** reference run INCOMPLETE: {len(cen) - len(common)} rows not yet measured; "
          f"every number below is over the {len(common)} measured rows only **")

ours_dec = [f for f in common if cen[f]["verdict"] in DEC]
und = [f for f in common if cen[f]["verdict"] not in DEC]
z3d = sum(1 for f in common if ref[f]["z3"] in DEC)
cvd = sum(1 for f in common if ref[f]["cvc5"] in DEC)
best = sum(1 for f in common if ref[f]["z3"] in DEC or ref[f]["cvc5"] in DEC)
print(f"\nover the {len(common)} common rows: ours={len(ours_dec)} z3={z3d} cvc5={cvd} "
      f"best-of-two={best}")
print(f"gap to best-of-two = {best - len(ours_dec)}")

addr = [f for f in und if ref[f]["z3"] in DEC or ref[f]["cvc5"] in DEC]
noone = [f for f in und if f not in addr]
print(f"\nof OUR {len(und)} undecided rows:")
print(f"  ADDRESSABLE (a reference decides it):        {len(addr)}")
print(f"  nobody decides it (not a prize, ever):       {len(noone)}")

print(f"\n== census cause x addressability (the number that sizes the work) ==")
g = defaultdict(lambda: [0, 0])
for f in und:
    g[cen[f]["bucket"]][0 if f in addr else 1] += 1
print(f"{'addressable':>11} {'nobody':>7}  bucket")
for b, (a, n) in sorted(g.items(), key=lambda kv: -kv[1][0]):
    print(f"{a:>11} {n:>7}  {b}")

# Soundness of the reference run itself: a reference that disagrees with the
# declared status would make every number above suspect.
comp = dis = 0
for f in common:
    for k in ("z3", "cvc5"):
        if ref[f][k] in DEC and ref[f]["status"] in DEC:
            comp += 1
            if ref[f][k] != ref[f]["status"]:
                dis += 1
                print(f"  REFERENCE DISAGREEMENT {k}={ref[f][k]} status={ref[f]['status']} {f}")
print(f"\nreference vs declared :status -- comparable={comp} disagreements={dis}")
