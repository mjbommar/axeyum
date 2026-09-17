#!/usr/bin/env python3
"""Summarize a sizing sweep (`sizing-run.sh` output) by MECHANISM.

For each of the two census populations (the 27 "no tableau" rows and the 11
"disequality" rows) and each arm's TSV, bucket the files by
`(verdict, rc, online_probe, LRAMODELPROBE sites)`. `online_probe` is read from
the captured stdout (`--trace` prints the `; lazy-smt … online_probe=…` line
there); the probe sites come from stderr, already folded into the TSV.

Usage: sizing-summarize.py <workdir> <tag>...
"""
import collections
import csv
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
work = Path(sys.argv[1])
tags = sys.argv[2:]
pops = {
    "no-tableau-27": [l.strip() for l in (HERE / "no-tableau-27.txt").read_text().splitlines() if l.strip()],
    "diseq-11": [l.strip() for l in (HERE / "diseq-11.txt").read_text().splitlines() if l.strip()],
}
for tag in tags:
    tsv = work / f"{tag}.tsv"
    rows = {r["file"]: r for r in csv.DictReader(open(tsv), delimiter="\t")}
    print(f"===== {tag}: {len(rows)} rows")
    for name, lst in pops.items():
        c = collections.Counter()
        eqf = []
        for f in lst:
            r = rows.get(f)
            if not r:
                c["MISSING"] += 1
                continue
            cap = work / "cap" / f"{tag}.{f.replace('/', '_')}"
            out = cap.with_suffix(cap.suffix + ".out").read_text() if cap.with_suffix(cap.suffix + ".out").exists() else ""
            probe = re.findall(r"online_probe=([a-z_-]+)", out)
            probe = probe[-1] if probe else "n/a"
            c[(r["verdict"], r["rc"], probe, r["probe_sites"])] += 1
            if r["eq_false"] != "n/a":
                eqf.append((f.rsplit("/", 1)[1], r["equalities"], r["eq_false"], r["diseq_violated"]))
        print(f"  {name}:")
        for k, v in sorted(c.items(), key=lambda kv: -kv[1]):
            print(f"    {v:3d}  {k}")
        if eqf:
            print("    equalities / asserted-false / violated-at-point per file:")
            for row in eqf:
                print(f"      {row[0]:<40} {row[1]:>5} {row[2]:>5} {row[3]:>5}")
