#!/usr/bin/env python3
"""Score the committed SIZING against the A/B that followed it.

    python3 bench-results/dt-valued-result-20260912/score-prediction.py

The sizing note was committed BEFORE the implementation, so this is a real
prediction being scored and not a fit. It prints where each gain fell relative
to the two predicates the note bracketed with, and how many gains lie in the
`is`/`select`-over-a-non-variable bucket the note flagged as an UNQUANTIFIED
addition the predicate structurally could not see.
"""

import collections
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
PREFIX = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
DIVS = ["AUFDTLIRA", "UFDTLIRA", "UFDT"]

import importlib.util

spec = importlib.util.spec_from_file_location("ac", os.path.join(HERE, "analyze-census.py"))
ac = importlib.util.module_from_spec(spec)
_stdout = sys.stdout
sys.stdout = open(os.devnull, "w")
try:
    spec.loader.exec_module(ac)
finally:
    sys.stdout.close()
    sys.stdout = _stdout

census = {(r["div"], r["path"]): r for r in ac.rows}

gains = []
for div in DIVS:
    p = os.path.join(HERE, "ab", "out", f"{div}.tsv")
    with open(p, encoding="utf-8", errors="replace") as fh:
        fh.readline()
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if len(parts) != 8:
                continue
            f, base, _, _, new, _, _, _ = parts
            if base not in ("sat", "unsat") and new in ("sat", "unsat"):
                gains.append((div, f.replace(PREFIX, "")))

print(f"gains: {len(gains)}")
missing = [g for g in gains if g not in census]
print(f"gains with no census row: {len(missing)}")
for g in missing:
    print("   ", g)

buckets = collections.Counter()
inside_any = inside_every = newly_any = 0
for g in gains:
    r = census.get(g)
    if not r:
        continue
    buckets[r["bucket"]] += 1
    inside_any += r["any_c"]
    inside_every += r["all_c"]
    newly_any += r["any_c"] and not r["any_a"]

print()
print("  the committed bracket was [0, 52] newly-ANY-eligible,")
print("  with a point estimate of 'low teens' and an unquantified addition.")
print()
print(f"  gains inside the ANY-entry eligibility predicate   : {inside_any} of {len(gains)}")
print(f"  gains inside the EVERY-entry predicate             : {inside_every} of {len(gains)}")
print(f"  gains that were NEWLY ANY-eligible                 : {newly_any} of {len(gains)}")
print()
print("  the base-arm bucket each gain came from:")
for b, n in buckets.most_common():
    print(f"    {n:>3}  {b}")
