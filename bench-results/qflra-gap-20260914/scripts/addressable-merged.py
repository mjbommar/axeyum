#!/usr/bin/env python3
"""Addressability with the idle-host re-take folded in.

The first reference pass ran six concurrent shards on s4 and read z3 = 155
against the canonical board's 166.  Load can only make a deadline-bounded
solver decide FEWER files, so it understated addressability; the rows it
understated are exactly the ones it called "decided by nobody", and those were
re-taken on idle hosts one pinned pair each.

This merges the two passes by taking, per file and per solver, the BEST verdict
observed -- which is the right rule for an addressability question ("can any
reference decide this at this budget?") and the wrong one for a head-to-head
score, so the merged numbers are used only for sizing.

Usage: addressable-merged.py <census-rows.tsv> --ref <ref.tsv...> --recheck <nobody.tsv...>
"""
import sys
from collections import defaultdict

DEC = ("sat", "unsat")
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"

argv = sys.argv[1:]
cen_path = argv[0]
ri, ci = argv.index("--ref"), argv.index("--recheck")
ref_paths, re_paths = argv[ri + 1:ci], argv[ci + 1:]

cen = {}
with open(cen_path) as fh:
    head = fh.readline().rstrip("\n").split("\t")
    for line in fh:
        r = dict(zip(head, line.rstrip("\n").split("\t")))
        cen[r["file"]] = r

best = defaultdict(lambda: {"z3": "none", "cvc5": "none", "status": "none"})
for paths in (ref_paths, re_paths):
    for p in paths:
        with open(p) as fh:
            head = fh.readline().rstrip("\n").split("\t")
            for line in fh:
                r = dict(zip(head, line.rstrip("\n").split("\t")))
                rel = r["file"].replace(CORPUS, "")
                for k in ("z3", "cvc5"):
                    if r.get(k) in DEC:
                        best[rel][k] = r[k]
                if r.get("status", "none") != "none":
                    best[rel]["status"] = r["status"]

common = sorted(set(cen) & set(best))
ours = sum(1 for f in common if cen[f]["verdict"] in DEC)
z3d = sum(1 for f in common if best[f]["z3"] in DEC)
cvd = sum(1 for f in common if best[f]["cvc5"] in DEC)
bo = sum(1 for f in common if best[f]["z3"] in DEC or best[f]["cvc5"] in DEC)
print(f"rows={len(common)}   ours={ours}   z3={z3d}   cvc5={cvd}   best-of-two={bo}")
print(f"gap to best-of-two = {bo - ours}")

und = [f for f in common if cen[f]["verdict"] not in DEC]
addr = [f for f in und if best[f]["z3"] in DEC or best[f]["cvc5"] in DEC]
print(f"\nof OUR {len(und)} undecided rows: ADDRESSABLE={len(addr)}  "
      f"decided by nobody={len(und) - len(addr)}")

print(f"\n== census cause x addressability (THE sizing number) ==")
g = defaultdict(lambda: [0, 0])
for f in und:
    g[cen[f]["bucket"]][0 if f in addr else 1] += 1
print(f"{'addressable':>11} {'nobody':>7}  bucket")
for b, (a, n) in sorted(g.items(), key=lambda kv: -kv[1][0]):
    print(f"{a:>11} {n:>7}  {b}")

comp = dis = 0
for f in common:
    for k in ("z3", "cvc5"):
        if best[f][k] in DEC and best[f]["status"] in DEC:
            comp += 1
            if best[f][k] != best[f]["status"]:
                dis += 1
                print(f"  REFERENCE DISAGREEMENT {k}={best[f][k]} status={best[f]['status']} {f}")
print(f"\nreference vs declared :status -- comparable={comp} disagreements={dis}")
