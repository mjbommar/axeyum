#!/usr/bin/env python3
"""Reproduce every number in the ADR-1942 sizing note from the committed rows.

Reads `census/<division>.tsv` (the compacted records this directory ships) and
prints the three tables the note quotes. Run with no arguments from anywhere:

    python3 bench-results/dt-constructor-arg-20260912/analyze-census.py

A record is one entry of `collect_ackermann_groups`' classification of EVERY
datatype-sorted uninterpreted-function argument in the query -- not the first
refusal, which is what makes this a reachability count rather than a blocker
count.
"""

import collections
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CENSUS = os.path.join(HERE, "census")
DIVS = ["AUFDTLIRA", "UFDTLIRA", "UFDT"]

# The two spellings of the refusal this lane targets: ADR-1935's, and the
# narrower one ADR-1942 replaced it with.
TARGET_REFUSALS = (
    "not a free variable",
    "neither a free variable nor a constructor",
)


def load(div):
    """-> {path: {"verdict", "giveup", "recs": [dict]}}"""
    out = {}
    with open(os.path.join(CENSUS, f"{div}.tsv")) as fh:
        for line in fh:
            if line.startswith("#"):
                continue
            p = line.rstrip("\n").split("\t")
            if p[0] == "F":
                out.setdefault(p[1], {"recs": []})
                out[p[1]]["verdict"] = p[2]
                out[p[1]]["giveup"] = p[3]
            elif p[0] == "C":
                rec = {}
                for tok in p[3].split()[1:]:
                    k, _, v = tok.partition("=")
                    rec[k] = v
                out.setdefault(p[1], {"recs": []})["recs"].append(rec)
    return out


def bucket(row):
    if row["verdict"] in ("sat", "unsat"):
        return "decided"
    g = row["giveup"]
    if any(t in g for t in TARGET_REFUSALS):
        return "non-variable dt argument"
    if "expansion is not exact" in g:
        return "inexact expansion"
    if "RESULT sort mentions a datatype" in g:
        return "dt-valued UF result"
    if "non-variable datatype term" in g:
        return "is/select non-variable"
    if g in ("WRAPPER-KILLED", "RC134-ABORT", "SIGKILL", "none"):
        return g
    m = re.search(r"detail=(.*)", g)
    return "other: " + (m.group(1) if m else g)[:52]


def total(recs, key):
    return sum(int(r.get(key, 0)) for r in recs)


def every(recs, key):
    return bool(recs) and all(r.get(key) == "1" for r in recs)


rows = []
for div in DIVS:
    for path, row in load(div).items():
        recs = row["recs"]
        rows.append(
            dict(
                div=div,
                path=path,
                bucket=bucket(row),
                elig_a=every(recs, "ELIGIBLE"),
                elig_b=every(recs, "ELIGIBLE_B"),
                has_ctor=total(recs, "ctor_exact") + total(recs, "ctor_inexact") > 0,
                has_apply=total(recs, "apply_exact") + total(recs, "apply_inexact") > 0,
                ctor_inexact=total(recs, "ctor_inexact") > 0,
                sym_inexact=total(recs, "sym_inexact") > 0,
                other=total(recs, "other") > 0,
                kinds={
                    k
                    for r in recs
                    for k in r.get("other_kinds", "-").split(",")
                    if k and k != "-"
                },
            )
        )

assert len(rows) == 600, f"expected 600 rows, got {len(rows)}"

TARGET = lambda r: r["bucket"] == "non-variable dt argument"


def line(label, pred, subset=None):
    per = collections.Counter()
    for r in rows:
        if subset and not subset(r):
            continue
        if pred(r):
            per[r["div"]] += 1
    print(f"  {label:56} " + " ".join(f"{per[d]:>6}" for d in DIVS) + f" {sum(per.values()):>7}")


print("                                                           " + " ".join(f"{d:>6}" for d in DIVS) + "   total")
print()
print("=== 1. Where the 600 stand on the ADR-1935 arm ===\n")
counts = collections.Counter(r["bucket"] for r in rows)
for b, _ in counts.most_common(8):
    line(b, lambda r, b=b: r["bucket"] == b)

print("\n=== 2. The 173, classified by what ELSE blocks them ===\n")
line("files whose first refusal is the non-variable dt argument", TARGET)
line("SLICE A eligible (ADR-1942: constructor arguments)", lambda r: r["elig_a"], TARGET)
line("blocked by an Op::Apply datatype argument", lambda r: r["has_apply"], TARGET)
line("blocked by a constructor over an INEXACT datatype", lambda r: r["ctor_inexact"], TARGET)
line("blocked by a VARIABLE over an inexact datatype", lambda r: r["sym_inexact"], TARGET)
line("blocked by some other term shape", lambda r: r["other"], TARGET)
shapes = sorted({k for r in rows if TARGET(r) for k in r["kinds"]})
print(f"  other shapes seen: {shapes}")

print("\n=== 3. The next rung priced, and whether A is its prerequisite ===\n")
line("SLICE B eligible (also Ackermannise a dt-VALUED result)", lambda r: r["elig_b"], TARGET)
line("  ... and ALSO has a constructor argument (needs A first)",
     lambda r: r["elig_b"] and r["has_ctor"], TARGET)
line("  ... and has none (slice B on its own)",
     lambda r: r["elig_b"] and not r["has_ctor"], TARGET)
print()
line("SLICE B eligible, across all 600", lambda r: r["elig_b"])
line("SLICE A eligible, across all 600", lambda r: r["elig_a"])
line("any constructor datatype argument at all, across all 600", lambda r: r["has_ctor"])

print("\n=== 4. The slice-A population, named ===\n")
for r in sorted((r for r in rows if r["elig_a"]), key=lambda r: (r["div"], r["path"])):
    print(f"  {r['div']:10} {r['bucket']:26} {r['path']}")
