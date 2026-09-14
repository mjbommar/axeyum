#!/usr/bin/env python3
"""SKELETON-REACH -- the 7 `fd:parse` rows, base arm against treatment arm.

    fd-rows-across-arms.py <lane-dir>

Writes `lists/moved-rows.list` and `ref/new-verdicts.tsv` as a side effect, so
the R5 re-run and the authority check both consume what THIS run measured
rather than a list typed by hand.

The point of the table is that the treatment removes the INGEST REFUSAL on all
seven and converts only two: on the rest the file now reaches the ladder and
the budget goes somewhere else. Reporting only the +2 would hide that the
mechanism fired seven times.
"""
import csv
import sys

LANE = sys.argv[1] if len(sys.argv) > 1 else "."
F = ["file", "base_v", "base_rung", "base_ms", "base_giveup",
     "arm_v", "arm_rung", "arm_ms", "arm_giveup", "order"]
C = ["file", "verdict", "bound_by", "last", "attempts", "ms", "giveup_kind", "skel_rung", "giveup_raw"]
DEC = {"sat", "unsat"}

ab = {r["file"]: r for r in csv.DictReader(open(f"{LANE}/ref/ab-treatment-ufnia-200.tsv"),
                                           delimiter="\t", fieldnames=F)}
# UNDECIDED rows only. `bound_by == "fd:parse"` alone returns 9, because two
# `sledgehammer` files are DECIDED `unsat` and merely spent their longest stage
# in parsing -- a correct attribution, and not a stop. Filtering on the verdict
# is what makes this the same 7 the census counted; without it the two tables
# in this lane disagree by 2 and neither is wrong.
cen = [r for r in csv.DictReader(open(f"{LANE}/ref/fd-census-208.tsv"), delimiter="\t", fieldnames=C)
       if r["bound_by"] == "fd:parse" and r["verdict"] not in DEC]

print(f"the {len(cen)} fd:parse rows, base arm vs treatment arm:")
print(f"  {'base cause':<14} {'base':<8} {'arm':<8} {'arm rung':<9} {'arm giveup':<12} file")
moved = []
for r in cen:
    a = ab[r["file"]]
    print(f"  {r['giveup_kind']:<14} {a['base_v']:<8} {a['arm_v']:<8} {a['arm_rung']:<9} "
          f"{a['arm_giveup']:<12} {r['file'].split('/', 1)[1][:50]}")
    if a["base_v"] not in DEC and a["arm_v"] in DEC:
        moved.append((r["file"], a["arm_v"]))

with open(f"{LANE}/lists/moved-rows.list", "w") as fh:
    fh.write("".join(f"{f}\n" for f, _ in moved))
with open(f"{LANE}/ref/new-verdicts.tsv", "w") as fh:
    fh.write("".join(f"{f}\t{v}\n" for f, v in moved))
print(f"\nmoved rows: {len(moved)}  -> lists/moved-rows.list, ref/new-verdicts.tsv")
