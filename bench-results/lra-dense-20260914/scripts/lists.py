#!/usr/bin/env python3
"""Derive this lane's populations from ADR-2045's committed census + references.

Populations, all defined from ADR-2045's data and BEFORE any measurement of
this lane's own:

  ALL200   the whole QF_LRA board division (the A/B population)
  DENSE74  the offline dense-matrix LRA engine rows: bucket ABORT/oom (40)
           + bucket Timeout/ResourceLimit minus the lazy-SMT wall-clock row(s),
           which ADR-2045 counts in that bucket but attributes to another engine
  DENSE50  the ADDRESSABLE subset of DENSE74 -- the 82 % prize

Addressability uses ADR-2045's merged rule (best verdict per file per solver
over the loaded pass AND the idle re-take), which is its sizing rule and the
wrong rule for a head-to-head score.

Usage: lists.py <out-dir>
"""

import glob
import os
import sys
from collections import defaultdict

BASE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "qflra-gap-20260914")
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
DEC = ("sat", "unsat")
OUT = sys.argv[1]

cen = {}
with open(os.path.join(BASE, "census-rows.tsv")) as fh:
    head = fh.readline().rstrip("\n").split("\t")
    for line in fh:
        r = dict(zip(head, line.rstrip("\n").split("\t")))
        cen[r["file"]] = r

best = defaultdict(lambda: {"z3": "none", "cvc5": "none"})
for p in sorted(glob.glob(os.path.join(BASE, "ref", "*.tsv"))):
    with open(p) as fh:
        head = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            r = dict(zip(head, line.rstrip("\n").split("\t")))
            rel = r["file"].replace(CORPUS, "")
            for k in ("z3", "cvc5"):
                if r.get(k) in DEC:
                    best[rel][k] = r[k]


def addressable(f):
    return best[f]["z3"] in DEC or best[f]["cvc5"] in DEC


allrows = sorted(cen)
und = [f for f in allrows if cen[f]["verdict"] not in DEC]
abort_half = [f for f in und if cen[f]["bucket"] == "ABORT/oom"]
clock = [f for f in und if cen[f]["bucket"] == "Timeout/ResourceLimit"]
lazy = [f for f in clock if "lazy" in cen[f]["cause"].lower()]
dense74 = sorted(abort_half + [f for f in clock if f not in lazy])
dense50 = [f for f in dense74 if addressable(f)]


def write(name, rows):
    with open(os.path.join(OUT, name), "w") as fh:
        for f in rows:
            fh.write(CORPUS + f + "\n")
    print(f"{name:12s} n={len(rows)}")


write("ALL200.txt", allrows)
write("DENSE74.txt", dense74)
write("DENSE50.txt", dense50)
print(
    f"  (abort half={len(abort_half)}  clock half={len(dense74) - len(abort_half)}  "
    f"lazy-SMT excluded={len(lazy)})"
)
print(f"  DENSE74 addressable={len(dense50)}  nobody={len(dense74) - len(dense50)}")
