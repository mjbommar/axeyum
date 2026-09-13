#!/usr/bin/env python3
"""Count the solver runs behind this lane, from the artifacts rather than from
arithmetic on what the sweeps were supposed to have done."""
import glob
import os
import sys

root = sys.argv[1]
total_ax = 0
total_ref = 0
for name in sorted(os.listdir(f"{root}/out")):
    d = f"{root}/out/{name}"
    if not os.path.isdir(d):
        continue
    n = 0
    for p in glob.glob(f"{d}/*.tsv"):
        with open(p) as fh:
            n += sum(1 for _ in fh) - 1
    # `verify` rows carry THREE solver runs each (axeyum, z3, cvc5).
    if name == "verify":
        print(f"  {name:<12} {n:>6} rows x 3 solvers = {n * 3} runs")
        total_ax += n
        total_ref += n * 2
    else:
        print(f"  {name:<12} {n:>6} axeyum runs")
        total_ax += n
print(f"\naxeyum runs      {total_ax}")
print(f"reference runs   {total_ref}  (z3 + cvc5, verification only)")
print(f"TOTAL            {total_ax + total_ref}")
