#!/usr/bin/env python3
"""SKELETON-REACH -- the two censuses, joined.

    summarize-census.py <lane-dir>

Prints, in order:

  1. UFNIA re-derived verdicts and `bound_by` over its undecided rows.
  2. The `fd:parse` bucket SPLIT by the raw give-up detail, never by the label.
  3. The 13 skeleton-unsat rows against what our own binary does with them,
     which is the absent / not-reached / not-refutable decomposition:
        rung `absent`   -> NOT REACHED
        rung `declined` -> reached and NOT REFUTABLE by our ground checker
        rung `decided`  -> converted (there should be none left: these are
                           rows still undecided on the shipped default)
"""
import collections
import csv
import re
import sys

LANE = sys.argv[1] if len(sys.argv) > 1 else "."
F = ["file", "verdict", "bound_by", "last", "attempts", "ms", "giveup_kind", "skel_rung", "giveup_raw"]
S = ["file", "shape", "occ", "atoms", "cvc5", "z3", "cms", "zms"]

rows = list(csv.DictReader(open(f"{LANE}/ref/fd-census-208.tsv"), delimiter="\t", fieldnames=F))
idx = {r["file"]: r for r in rows}
skel = list(csv.DictReader(open(f"{LANE}/ref/skeleton-census-655.tsv"), delimiter="\t", fieldnames=S))
sk = [r["file"] for r in skel if r["shape"] == "PRESENT" and r["cvc5"] == "unsat" and r["z3"] == "unsat"]
sks = set(sk)

ufnia = [r for r in rows if r["file"].startswith("UFNIA/")]
print(f"UFNIA rows re-derived in this run: {len(ufnia)}")
print("  verdicts:", dict(collections.Counter(r["verdict"] for r in ufnia)))
und = [r for r in ufnia if r["verdict"] == "unknown"]
print(f"\n1. bound_by over the {len(und)} undecided UFNIA rows")
for k, v in collections.Counter(r["bound_by"] for r in und).most_common():
    print(f"     {v:>4}  {k}")

fdp = [r for r in und if r["bound_by"] == "fd:parse"]
print(f"\n2. the fd:parse bucket is {len(fdp)} rows, and it is NOT one cause")
print("     kind:", dict(collections.Counter(r["giveup_kind"] for r in fdp)))
for k, v in collections.Counter(re.sub(r"\d+", "N", r["giveup_raw"])[:104] for r in fdp).most_common():
    print(f"     {v:>4}  {k}")
print(f"\n     per row (skel-unsat = the static instrument's verdict on its skeleton):")
for r in fdp:
    tag = "YES" if r["file"] in sks else "no"
    print(f"     {r['giveup_kind']:<13} skel-unsat={tag:<4} {r['ms']:>5}ms  {r['file'].split('/', 1)[1][:70]}")

print(f"\n3. the {len(sk)} skeleton-unsat rows against our own binary")
print(f"     {'division':<10} {'verdict':<8} {'rung':<9} {'bound_by':<24} {'ms':>6}  file")
cls = collections.Counter()
for f in sk:
    r = idx.get(f)
    d = f.split("/")[0]
    if not r:
        print(f"     {d:<10} {'--':<8} {'--':<9} {'NOT IN THIS CENSUS':<24} {'':>6}  {f.split('/', 1)[1][:56]}")
        cls["NOT-IN-CENSUS"] += 1
        continue
    kind = {"absent": "NOT-REACHED", "declined": "NOT-REFUTABLE", "decided": "CONVERTED"}[r["skel_rung"]]
    cls[kind] += 1
    print(f"     {d:<10} {r['verdict']:<8} {r['skel_rung']:<9} {r['bound_by']:<24} {r['ms']:>6}  {f.split('/', 1)[1][:56]}")
print("\n     decomposition:", dict(cls))
