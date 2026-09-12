#!/usr/bin/env python3
"""Derive the QF_NIA winnable population from the 2026-09-11 board and resolve
each basename to exactly one corpus path.  Lane qf-nia-dispatch."""
import csv
import collections
import os
import sys

import subprocess as _sp
ROOT = _sp.run(["git", "rev-parse", "--show-toplevel"],
               capture_output=True, text=True,
               cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
BOARD = os.path.join(ROOT, "bench-results/session-20260911-smtlib/head-to-head/QF_NIA.tsv")
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/QF_NIA"
PRIOR = os.path.join(ROOT, "bench-results/qf-nia-width-20260912/ab-winnable.tsv")
OUT = sys.argv[1]

DEC = {"sat", "unsat"}
rows = list(csv.DictReader(open(BOARD), delimiter="\t"))
print("board rows:", len(rows))
winnable = [r for r in rows if r["axeyum"] not in DEC and (r["z3"] in DEC or r["cvc5"] in DEC)]
ours = [r for r in rows if r["axeyum"] in DEC]
nobody = [r for r in rows if r["axeyum"] not in DEC and r["z3"] not in DEC and r["cvc5"] not in DEC]
print("we decide:", len(ours), " winnable:", len(winnable), " nobody:", len(nobody))

# resolve basenames against the corpus subtree
index = collections.defaultdict(list)
for dirpath, _dirs, files in os.walk(CORPUS):
    for f in files:
        if f.endswith(".smt2"):
            index[f].append(os.path.join(dirpath, f))
print("corpus files:", sum(len(v) for v in index.values()))

missing = [r["file"] for r in winnable if r["file"] not in index]
ambiguous = [r["file"] for r in winnable if len(index.get(r["file"], [])) > 1]
print("missing:", len(missing), "ambiguous:", len(ambiguous))
if missing:
    print("  e.g.", missing[:3])
if ambiguous:
    print("  e.g.", ambiguous[:3])

paths = {}
for r in winnable:
    cands = index.get(r["file"], [])
    if len(cands) == 1:
        paths[r["file"]] = cands[0]

prior = set()
for r in csv.DictReader(open(PRIOR), delimiter="\t"):
    prior.add(r["file"])
print("prior lane winnable paths:", len(prior))
mine = set(paths.values())
print("in mine not prior:", len(mine - prior))
for p in sorted(mine - prior)[:5]:
    print("   +", p)
print("in prior not mine:", len(prior - mine))
for p in sorted(prior - mine)[:5]:
    print("   -", p)

with open(OUT, "w") as fh:
    for r in winnable:
        fh.write(paths[r["file"]] + "\n")
print("wrote", OUT, len(winnable), "paths")

# family breakdown so a path-sorted list is not read as one family
fam = collections.Counter(
    os.path.relpath(paths[r["file"]], CORPUS).split("/")[0] for r in winnable
)
print("families:")
for k, v in fam.most_common():
    print(f"  {k:40s} {v}")
