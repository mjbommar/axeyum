#!/usr/bin/env python3
"""The cost population: files we ALREADY DECIDE in the integer-bearing divisions
a no-overflow side-constraint on `int_add`/`int_sub`/`int_neg` would tax.

Sampled every fourth already-decided file per division, exactly as ADR-1921 did,
so the two cost measurements are comparable.
"""
import collections
import csv
import os
import sys

import subprocess as _sp
ROOT = _sp.run(["git", "rev-parse", "--show-toplevel"],
               capture_output=True, text=True,
               cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
BOARDS = os.path.join(ROOT, "bench-results/session-20260911-smtlib/head-to-head")
CORPUS_ROOT = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"
# Every division whose queries can carry `Int` terms. QF_BV/QF_FP/QF_UF/QF_S are
# excluded because no `int_add` reaches the blaster from them.
DIVISIONS = ["QF_LIA", "QF_UFLIA", "QF_IDL", "QF_RDL", "QF_NRA", "QF_ABV",
             "QF_SLIA", "QF_DT", "UF"]
DEC = {"sat", "unsat"}
STRIDE = 4

out = sys.argv[1]
index = collections.defaultdict(list)
for div in DIVISIONS:
    root = os.path.join(CORPUS_ROOT, div)
    if not os.path.isdir(root):
        print("  (no corpus dir)", div)
        continue
    for dirpath, _d, files in os.walk(root):
        for f in files:
            if f.endswith(".smt2"):
                index[(div, f)].append(os.path.join(dirpath, f))

paths = []
per_div = collections.Counter()
for div in DIVISIONS:
    board = os.path.join(BOARDS, f"{div}.tsv")
    if not os.path.exists(board):
        print("  (no board)", div)
        continue
    rows = [r for r in csv.DictReader(open(board), delimiter="\t")
            if r["axeyum"] in DEC]
    # RESOLVE FIRST, THEN SAMPLE. Sampling first and dropping what will not
    # resolve makes the sample size a function of basename collisions rather
    # than of the division: QF_LIA lost 23 of 30 that way, because 92 of its
    # 119 decided rows share a basename with another directory and the board
    # cannot say which one it ran.
    uniq = [r for r in rows if len(index.get((div, r["file"]), [])) == 1]
    ambiguous = len(rows) - uniq.__len__()
    picked = uniq if len(uniq) < 40 else uniq[::STRIDE]
    for r in picked:
        paths.append(index[(div, r["file"])][0])
    per_div[div] = len(picked)
    print(f"  {div}: {len(rows)} decided, {len(uniq)} uniquely resolvable "
          f"({ambiguous} ambiguous basenames), {len(picked)} sampled")

with open(out, "w") as fh:
    fh.write("\n".join(paths) + "\n")
print("wrote", out, len(paths), "paths")
