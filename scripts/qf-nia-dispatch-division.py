#!/usr/bin/env python3
"""The whole QF_NIA division (200 files), resolved to corpus paths."""
import collections
import csv
import os
import sys

import subprocess as _sp
ROOT = _sp.run(["git", "rev-parse", "--show-toplevel"],
               capture_output=True, text=True,
               cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
BOARD = os.path.join(ROOT, "bench-results/session-20260911-smtlib/head-to-head/QF_NIA.tsv")
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/QF_NIA"

index = collections.defaultdict(list)
for dirpath, _d, files in os.walk(CORPUS):
    for f in files:
        if f.endswith(".smt2"):
            index[f].append(os.path.join(dirpath, f))

rows = list(csv.DictReader(open(BOARD), delimiter="\t"))
out = sys.argv[1]
absent = [r["file"] for r in rows if not index.get(r["file"])]
ambiguous = [r["file"] for r in rows if len(index.get(r["file"], [])) > 1]
print("board rows:", len(rows), "absent:", len(absent), "ambiguous:", len(ambiguous))
assert not absent, absent[:3]
# An AMBIGUOUS basename is included as BOTH candidate paths rather than dropped
# or guessed: the board cannot say which directory it came from, and a guess
# would put a file in the A/B under a row that is not its own. `106.smt2` is the
# only one in this division (mcm/ and 20170427-VeryMax/SAT14/) and its board row
# is `unknown` for all three solvers, so neither copy can produce a gain or a
# loss against a reference. Recorded, not silently resolved.
paths = []
for r in rows:
    paths.extend(index[r["file"]])
with open(out, "w") as fh:
    fh.write("\n".join(paths) + "\n")
print("wrote", out, len(paths), "paths for", len(rows), "board rows")
for b in ambiguous:
    print("  ambiguous, both included:", b, index[b])
