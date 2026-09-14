#!/usr/bin/env python3
"""Did the lever REACH the rung, or reach it and come out the other side?

ADR-2030's distinction.  A verdict count cannot tell the two apart and they have
completely different follow-ups: "still refused" means the bound is wrong, while
"admitted and still undecided" means the ENGINE is the wall and no bound will
move it.
"""
import sys
from collections import Counter

rows = []
for p in sys.argv[1:]:
    with open(p) as fh:
        head = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            rows.append(dict(zip(head, line.rstrip("\n").split("\t"))))

print(f"rows={len(rows)}  (the census's `online_probe=admission-screen` rows)")
print(f"\nprobe transition base -> arm:")
for (a, b), n in Counter((r["probe_base"], r["probe_arm"]) for r in rows).most_common():
    print(f"  {n:>3}  {a:<22} -> {b}")

still = sum(1 for r in rows if r["probe_arm"] == "admission-screen")
reached = sum(1 for r in rows if r["probe_arm"] not in ("admission-screen", "NONE"))
died = sum(1 for r in rows if r["probe_arm"] == "NONE")
print(f"\n  STILL REFUSED by the screen (bound is the wall):  {still}")
print(f"  REACHED the engine (engine is the wall):          {reached}")
print(f"  died with no report at all:                       {died}")

moved = [r for r in rows if r["verdict_base"] != r["verdict_arm"]]
newly = [r for r in rows if r["verdict_arm"] in ("sat", "unsat")
         and r["verdict_base"] not in ("sat", "unsat")]
print(f"\n  verdicts that changed at all: {len(moved)}")
print(f"  NEWLY DECIDED:                {len(newly)}")
for r in moved:
    print(f"    {r['verdict_base']} -> {r['verdict_arm']}  {r['file'].split('non-incremental/')[-1]}")
