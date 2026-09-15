#!/usr/bin/env python3
"""Re-split ADR-2045's dense-engine bucket on MILLISECONDS, not on call counts.

ADR-2045 established that the SIMPLEX ran and the elimination did not
(`cube_matrices=0`, `cube_simplex_calls>0` on 34 of 34 rows), and labelled the
bucket "dense simplex spent the budget". The first half is a measurement; the
second is an inference from a call counter, and a call counter says a thing
happened, not that it dominated.

`--trace`'s `; lazy-smt` line carries the milliseconds. This reports, per row
and over the population, which phase actually held the 24 s, over the DISJOINT
decomposition below -- the raw field names are NESTED and reading them as
siblings charges the dense engine's time twice.

A row is called DENSE-ENGINE-BOUND only when `cube_simplex_ms` is the largest
disjoint phase AND is at least half the accounted time. Anything else is named
by whatever actually held the budget.

Result on the 74-row dense-engine population: of the 34 rows that survive to
print a trace, **26 are dense-engine-bound and 7 are bound by the Boolean
SKELETON** -- the lazy-SMT loop re-solving a skeleton that emits over a thousand
cubes the theory then refutes one at a time. So ADR-2045's "34 of 34" is right
about which ENGINE ran and overstates how many rows that engine BOUND.

Usage: attrib.py <harness-dir>
"""

import glob
import os
import re
import statistics
import sys
from collections import Counter

KV = re.compile(r"(\w+)=([^\s]+)")

# THE COUNTERS NEST, AND READING THEM AS SIBLINGS DOUBLE-COUNTS.  Verified
# against the raw trace rather than assumed:
#
#   accounted_ms = skeleton_ms + theory_ms + core_ms + pending_round_ms
#   theory_ms   >= cube_collect_ms + cube_fm_ms + cube_simplex_ms
#
# On one measured row: 23 759 = 3 170 + 20 575 + 13 + 0, and
# 20 575 >= 796 + 0 + 19 754.  So `cube_simplex_ms` is a BREAKDOWN of
# `theory_ms`, not a phase beside it, and a "which is biggest" over the raw
# field names charges the dense engine's time to the theory twice.  The first
# draft of this script did exactly that and reported 0 of 34 dense-engine-bound
# rows; the disjoint decomposition below reports something different.
DISJOINT = (
    "skeleton_ms",      # the Boolean skeleton the lazy-SMT loop re-solves
    "cube_simplex_ms",  # THE OFFLINE DENSE ENGINE -- the handoff's named cause
    "cube_fm_ms",       # Fourier-Motzkin, which ADR-2045 showed never runs here
    "cube_collect_ms",  # constraint collection
    "theory_other_ms",  # theory_ms minus the three cube_* above
    "core_ms",
)


def main():
    rows = []
    for d in sys.argv[1:]:
        for tsv in sorted(glob.glob(os.path.join(d, "out", "attrib.sh*.tsv"))):
            with open(tsv) as fh:
                head = fh.readline().rstrip("\n").split("\t")
                for line in fh:
                    rows.append(dict(zip(head, line.rstrip("\n").split("\t"))))
    print(f"rows={len(rows)}")

    traced, untraced = [], []
    for r in rows:
        if r.get("lazy", "none") in ("none", ""):
            untraced.append(r)
            continue
        kv = dict(KV.findall(r["lazy"]))

        def g(name):
            v = kv.get(name, "0")
            return int(v) if v.isdigit() else 0

        cubes = g("cube_collect_ms") + g("cube_fm_ms") + g("cube_simplex_ms")
        r["_ms"] = {
            "skeleton_ms": g("skeleton_ms"),
            "cube_simplex_ms": g("cube_simplex_ms"),
            "cube_fm_ms": g("cube_fm_ms"),
            "cube_collect_ms": g("cube_collect_ms"),
            "theory_other_ms": max(g("theory_ms") - cubes, 0),
            "core_ms": g("core_ms"),
        }
        r["_acct"] = int(kv.get("accounted_ms", 0) or 0)
        r["_rounds"] = int(kv.get("lra_rounds", 0) or 0)
        r["_blocking"] = int(kv.get("blocking_clauses", 0) or 0)
        r["_atoms"] = int(kv.get("atoms", 0) or 0)
        r["_probe"] = kv.get("online_probe", "na")
        traced.append(r)

    print(f"  rows with a `; lazy-smt` trace line = {len(traced)}")
    print(f"  rows WITHOUT one = {len(untraced)}  (a process that aborts prints no trace)")
    if untraced:
        rc = Counter(r["rc"] for r in untraced)
        print(f"    their exit statuses: {dict(rc)}   (134 = abort)")
    if not traced:
        print("NO TRACED ROWS -- this measured nothing.")
        return 1

    def binding(r):
        if not r["_ms"]:
            return "no-phase-counters"
        top, ms = max(r["_ms"].items(), key=lambda kv: kv[1])
        total = sum(r["_ms"].values())
        if total == 0:
            return "zero-accounted"
        return top if ms >= 0.5 * total else f"mixed(top={top})"

    print("\n== WHICH PHASE HELD THE BUDGET, on the rows that could report ==")
    b = Counter(binding(r) for r in traced)
    for k, v in b.most_common():
        print(f"  {v:>3}  {k}")

    print("\n== the phases, as a share of accounted time ==")
    for p in DISJOINT:
        sh = sorted(
            100.0 * r["_ms"][p] / sum(r["_ms"].values())
            for r in traced
            if p in r["_ms"] and sum(r["_ms"].values()) > 0
        )
        if sh:
            print(
                f"  {p:<18} n={len(sh):>3}  median {statistics.median(sh):5.1f} %"
                f"   min {sh[0]:4.1f} %   max {sh[-1]:5.1f} %"
            )

    dense_bound = [r for r in traced if binding(r) == "cube_simplex_ms"]
    print(
        f"\n  DENSE-ENGINE-BOUND (cube_simplex_ms is top AND >= half): "
        f"{len(dense_bound)} of {len(traced)} traced rows"
    )

    sk = [r for r in traced if binding(r) == "skeleton_ms"]
    if sk:
        rounds = sorted(r["_rounds"] for r in sk)
        print(
            f"  SKELETON-BOUND: {len(sk)} rows, lazy-SMT rounds median "
            f"{statistics.median(rounds):,.0f}  max {rounds[-1]:,}"
        )

    print("\n== per row ==")
    print(
        f"{'rc':>3} {'acct_ms':>8} {'simplex':>8} {'simplex%':>8} {'skeleton':>9} "
        f"{'skel%':>6} {'th_oth':>7} {'rounds':>7} {'binding':>16}  file"
    )
    for r in sorted(traced, key=lambda x: -x["_ms"]["cube_simplex_ms"]):
        m = r["_ms"]
        tot = sum(m.values()) or 1
        print(
            f"{r['rc']:>3} {r['_acct']:>8,} "
            f"{m['cube_simplex_ms']:>8,} {100.0 * m['cube_simplex_ms'] / tot:7.1f}% "
            f"{m['skeleton_ms']:>9,} {100.0 * m['skeleton_ms'] / tot:5.1f}% "
            f"{m['theory_other_ms']:>7,} {r['_rounds']:>7,} {binding(r):>16}  "
            f"{os.path.basename(r['file'])[:52]}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
