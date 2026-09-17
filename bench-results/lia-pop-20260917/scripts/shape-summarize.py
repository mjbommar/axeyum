#!/usr/bin/env python3
"""Merge the shape-sweep shard TSVs (`run-shape-scripts.sh` output) into
`shape/sweep.tsv` (corpus files) and `shape/sweep_controls.tsv` (the two
fixtures), and print a per-logic summary. Exit 1 on any DISAGREE cell, or on
any file where A and B produced a different number of verdicts.

Usage: shape-summarize.py <out_dir> <shard.tsv>...
"""
import sys
from collections import defaultdict

CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/incremental/incremental/"
CONTROLS = "/nas3/data/axeyum/harness/lia-pop/shape/"


def main(out_dir, paths):
    header = None
    rows, controls = [], []
    for p in paths:
        with open(p, encoding="utf-8") as fh:
            h = fh.readline().rstrip("\n")
            header = header or h
            for line in fh:
                parts = line.rstrip("\n").split("\t")
                if len(parts) != len(h.split("\t")):
                    continue
                if parts[0].startswith(CONTROLS):
                    parts[0] = parts[0][len(CONTROLS):]
                    controls.append(parts)
                else:
                    parts[0] = parts[0].replace(CORPUS, "")
                    rows.append(parts)
    rows.sort()
    with open(f"{out_dir}/sweep.tsv", "w", encoding="utf-8") as fh:
        fh.write(header + "\n")
        for r in rows:
            fh.write("\t".join(r) + "\n")
    with open(f"{out_dir}/sweep_controls.tsv", "w", encoding="utf-8") as fh:
        fh.write(header + "\n")
        for r in controls:
            fh.write("\t".join(r) + "\n")

    per = defaultdict(lambda: defaultdict(int))
    bad = 0
    for r in rows:
        f, logic, an, bn, zn, a_z, b_z, a_b = r[:8]
        d = per[logic]
        d["files"] += 1
        d["A_verdicts"] += int(an)
        d["B_verdicts"] += int(bn)
        d["z3_verdicts"] += int(zn)
        if a_z == "agree":
            d["A_agree_z3"] += 1
        if b_z == "agree":
            d["B_agree_z3"] += 1
        if a_b == "agree":
            d["A_agree_B"] += 1
        if int(an) == 0:
            d["no_axeyum_output"] += 1
        if "DISAGREE" in (a_z, b_z, a_b) or an != bn:
            d["disagree"] += 1
            bad += 1
    cols = ["files", "A_agree_z3", "B_agree_z3", "A_agree_B", "no_axeyum_output", "disagree",
            "A_verdicts", "B_verdicts", "z3_verdicts"]
    print("| logic | " + " | ".join(cols) + " |")
    print("| --- | " + " | ".join("---:" for _ in cols) + " |")
    tot = defaultdict(int)
    for logic in sorted(per):
        d = per[logic]
        print(f"| {logic} | " + " | ".join(str(d[c]) for c in cols) + " |")
        for c in cols:
            tot[c] += d[c]
    print("| **all** | " + " | ".join(str(tot[c]) for c in cols) + " |")
    print(f"\nCONTROLS={len(controls)}")
    for r in controls:
        print("\t".join(r))
    print(f"DISAGREE_OR_COUNT_MISMATCH={bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1], sys.argv[2:]))
