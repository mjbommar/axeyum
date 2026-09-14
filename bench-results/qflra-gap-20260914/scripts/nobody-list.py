#!/usr/bin/env python3
"""Emit the corpus paths of rows WE do not decide and NO reference decided."""
import sys

DEC = ("sat", "unsat")
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"

cen = {}
with open(sys.argv[1]) as fh:
    head = fh.readline().rstrip("\n").split("\t")
    for line in fh:
        r = dict(zip(head, line.rstrip("\n").split("\t")))
        cen[r["file"]] = r

for p in sys.argv[2:]:
    with open(p) as fh:
        head = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            r = dict(zip(head, line.rstrip("\n").split("\t")))
            rel = r["file"].replace(CORPUS, "")
            c = cen.get(rel)
            if c and c["verdict"] not in DEC and r["z3"] not in DEC and r["cvc5"] not in DEC:
                print(r["file"])
