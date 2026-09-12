#!/usr/bin/env python3
"""Ground truth for the winnable population: declared :status vs the board's
z3/cvc5 verdicts.  A census is only useful if the files it censuses have an
uncontested expected answer."""
import collections
import csv
import os
import re

import subprocess as _sp
ROOT = _sp.run(["git", "rev-parse", "--show-toplevel"],
               capture_output=True, text=True,
               cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
BOARD = os.path.join(ROOT, "bench-results/session-20260911-smtlib/head-to-head/QF_NIA.tsv")
LIST = os.path.join(ROOT, ".lane/qf-nia-dispatch/winnable-110.txt")
STATUS_RE = re.compile(r"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)")

board = {r["file"]: r for r in csv.DictReader(open(BOARD), delimiter="\t")}
paths = [l.strip() for l in open(LIST) if l.strip()]
combo = collections.Counter()
decl = collections.Counter()
for p in paths:
    b = board[os.path.basename(p)]
    m = STATUS_RE.search(open(p, errors="replace").read())
    d = m.group(1) if m else "none"
    decl[d] += 1
    combo[(d, b["z3"], b["cvc5"])] += 1
print("declared :status:", dict(decl))
print("\n| declared | z3 | cvc5 | files |")
print("|---|---|---|---:|")
conflict = 0
for (d, z, c), n in combo.most_common():
    print(f"| {d} | {z} | {c} | {n} |")
    if z in ("sat", "unsat") and c in ("sat", "unsat") and z != c:
        conflict += n
    if d in ("sat", "unsat"):
        for o in (z, c):
            if o in ("sat", "unsat") and o != d:
                conflict += n
print("\nrows where an authority contradicts another:", conflict)
