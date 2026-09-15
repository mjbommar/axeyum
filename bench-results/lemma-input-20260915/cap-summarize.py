#!/usr/bin/env python3
"""LEMMA-INPUT -- what the INPUT CAP costs, read off the cap arm.

POLARITY: base = every lever unset; cap = `AXEYUM_LIA_INITIAL_BOUND_MUTEX_ATOM_CAP=1`,
which makes the mutex pass decline above 512 atoms.  A COST is a row decided
under base and not decided under cap.

Exit status depends on the finding: any cost exits non-zero.
"""

import collections
import pathlib
import sys

SRC = pathlib.Path(sys.argv[1])
DECIDED = pathlib.Path(sys.argv[2]) if len(sys.argv) > 2 else None
decided = set()
if DECIDED and DECIDED.is_file():
    decided = {ln.strip() for ln in DECIDED.read_text().splitlines() if ln.strip()}

runs = {}
for line in SRC.read_text().splitlines():
    if not line.strip():
        continue
    p = line.split("\t")
    if len(p) != 7:
        print(f"MALFORMED: {line!r}")
        sys.exit(4)
    runs[(p[1], p[2])] = (p[3], int(p[4]), int(p[5]))

files = sorted({k[0] for k in runs})
DEC = {"sat", "unsat"}
costs, gains, flips, status = [], [], [], []
for f in files:
    if (f, "base") not in runs or (f, "cap") not in runs:
        continue
    bv, bs, bw = runs[(f, "base")]
    cv, cs, cw = runs[(f, "cap")]
    if bv in DEC and cv not in DEC:
        costs.append((f, bv, cv, bw, cw))
    if bv not in DEC and cv in DEC:
        gains.append((f, bv, cv))
    if bv in DEC and cv in DEC and bv != cv:
        flips.append((f, bv, cv))
    if bs != cs:
        status.append((f, bs, cs))

print(f"rows with both arms: {sum(1 for f in files if (f, 'base') in runs and (f, 'cap') in runs)}")
print(f"  of which decided under base: {sum(1 for f in files if runs.get((f,'base'),('',0,0))[0] in DEC)}")
print()
print(f"COST  (decided -> undecided under the cap): {len(costs)}")
for f, bv, cv, bw, cw in costs:
    print(f"  {bv} -> {cv}\tbase={bw} ms cap={cw} ms\t{f}")
print(f"GAIN  (undecided -> decided under the cap): {len(gains)}")
for f, bv, cv in gains:
    print(f"  {bv} -> {cv}\t{f}")
print(f"FLIP  (sat <-> unsat):                      {len(flips)}")
for f, bv, cv in flips:
    print(f"  {bv} -> {cv}\t{f}")
print(f"EXIT-STATUS MOVES:                          {len(status)}")
for f, bs, cs in status:
    print(f"  {bs} -> {cs}\t{f}")
print()
for arm in ("base", "cap"):
    counts = collections.Counter(v[0] for k, v in runs.items() if k[1] == arm)
    print(f"verdicts {arm}: {dict(sorted(counts.items()))}")

if costs or flips:
    print()
    print("FINDING: enforcing the input cap changed a verdict.")
    sys.exit(1)
