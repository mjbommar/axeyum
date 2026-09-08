#!/usr/bin/env python3
"""Detail the distinct QF_LIA cost shapes from a sweep directory."""
import os
import re
import sys

sweep = sys.argv[1]
want = [
    "offline_calls", "offline_early_exits", "gomory_calls", "gomory_decided",
    "bnb_roots", "bnb_nodes", "bnb_budget_exhausted", "simplex_solves",
    "simplex_pivots", "simplex_declines", "lp_relaxations",
    "theory_asserts", "feasibility_checks", "core_minimizations",
]

rows = []
with open(os.path.join(sweep, "index.tsv"), encoding="utf-8") as fh:
    next(fh)
    for line in fh:
        n, path, verdict, wall = line.rstrip("\n").split("\t")
        text = open(os.path.join(sweep, f"{n}.log"), encoding="utf-8",
                    errors="replace").read()
        m = re.search(r"^; (?:partial )?lia .*$", text, re.M)
        if not m:
            continue
        fields = dict(re.findall(r"\b(\w+)=(\d+)\b", m.group(0)))
        route = re.search(r"\bbound_by=(\S+)", text)
        rows.append((os.path.basename(path), route.group(1) if route else "?",
                     int(wall), fields))

hdr = f"{'file':38s} {'bound_by':13s} " + " ".join(f"{k[:11]:>11s}" for k in want)
print(hdr)
print("-" * len(hdr))
for name, route, wall, f in sorted(rows, key=lambda r: (r[1], -r[2])):
    print(f"{name[:38]:38s} {route[:13]:13s} "
          + " ".join(f"{f.get(k, '-'):>11s}" for k in want))
