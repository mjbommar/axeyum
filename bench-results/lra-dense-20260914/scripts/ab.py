#!/usr/bin/env python3
"""Summarise the interleaved A/B, with an exit-status channel and a noise floor.

Polarity (must match `ab-run.sh`'s header):
  A   base       -- both levers UNSET, what ships today
  A2  base again -- the IDENTICAL configuration to A; A vs A2 IS the noise floor
  B   AXEYUM_LRA_SPARSE_ROWS=1
  C   AXEYUM_LRA_CELL_CAP=1
  D   both

Two things this reports that a verdict count cannot:

1. THE NOISE FLOOR, at ROW level and measured in THIS run. A and A2 are the same
   configuration on the same file on the same core, so every row they disagree
   on is noise. A count can be stable while rows move in both directions, so the
   row-level figure is the one that licenses calling a small net a null.

2. THE EXIT-STATUS CHANNEL. ADR-2045's arm was `losses=0` by verdict and created
   five new process ABORTS -- files that terminated cleanly in the base. A row
   that is `unknown` in both arms but aborts in one is a LOSS, and it is
   reported on its own line rather than folded into the net.

Usage: ab.py <harness-dir> <DIV>
"""

import glob
import math
import os
import sys
from collections import Counter

ARMS = ("A", "A2", "B", "C", "D")
DEC = ("sat", "unsat")


def wilson(k, n, z=1.96):
    """95 % Wilson interval for k of n; (nan, nan) when n is 0."""
    if n == 0:
        return float("nan"), float("nan")
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return max(0.0, c - h), min(1.0, c + h)


def main():
    root, div = sys.argv[1], sys.argv[2]
    rows = []
    for tsv in sorted(glob.glob(os.path.join(root, "out", f"ab.{div}.sh*.tsv"))):
        with open(tsv) as fh:
            head = fh.readline().rstrip("\n").split("\t")
            for line in fh:
                rows.append(dict(zip(head, line.rstrip("\n").split("\t"))))

    # An arm the runner did not execute writes `na`, and an arm that is not
    # DISTINGUISHED from one that ran and decided nothing reads as a catastrophic
    # regression: the first draft of this script reported the 2-arm control run
    # as "A2 net -148, noise floor 200 of 200 rows". Report unrun arms as DID NOT
    # RUN and exclude them from every figure.
    ran = [a for a in ARMS if any(r.get(a, "na") != "na" for r in rows)] if rows else []
    skipped = [a for a in ARMS if a not in ran]

    print(f"== A/B  division={div}  rows={len(rows)} ==")
    print("polarity: A = base (both levers UNSET, ships today); A2 = base repeated;")
    print("          B = SPARSE_ROWS; C = CELL_CAP; D = both")
    print("arm measures THIS BRANCH (the lane's worktree binary), 8 GiB / 24 s,")
    print("6 pinned pairs on s5/s6/s7, arms back to back per file, order rotating.\n")

    if not rows:
        print("NO ROWS -- this measured nothing.")
        return 1

    if skipped:
        print(f"ARMS NOT RUN in this division: {', '.join(skipped)} -- DID NOT RUN,")
        print("  reported as such and excluded below, never as a zero.\n")
    dec = {a: sum(1 for r in rows if r[a] in DEC) for a in ran}
    ab = {a: sum(1 for r in rows if r[f"{a}_rc"] == "134") for a in ran}
    kill = {a: sum(1 for r in rows if r[f"{a}_rc"] == "124") for a in ran}
    print(f"{'arm':>4} {'decided':>8} {'net vs A':>9} {'aborts':>7} {'wallkill':>9}")
    for a in ran:
        print(
            f"{a:>4} {dec[a]:>8} {dec[a] - dec['A']:>+9} {ab[a]:>7} {kill[a]:>9}"
        )

    # ---- the noise floor, measured here, at ROW level -------------------------
    if "A2" in ran:
        nf = [r for r in rows if r["A"] != r["A2"]]
        nf_rc = [r for r in rows if r["A_rc"] != r["A2_rc"]]
        print(
            f"\n== NOISE FLOOR (A vs A2, the SAME configuration) ==\n"
            f"  rows differing by VERDICT      : {len(nf)} of {len(rows)}\n"
            f"  rows differing by EXIT STATUS  : {len(nf_rc)} of {len(rows)}\n"
            f"  decided count A={dec['A']}  A2={dec['A2']}"
            f"  (a stable count can still hide moving rows)"
        )
        for r in nf[:10]:
            print(f"    NOISE {r['A']:>7} -> {r['A2']:>7}  {os.path.basename(r['file'])[:60]}")
        for r in nf_rc[:10]:
            print(f"    NOISE rc {r['A_rc']:>4} -> {r['A2_rc']:>4}  {os.path.basename(r['file'])[:56]}")
    else:
        print("\n== NOISE FLOOR: DID NOT RUN in this division (arm A2 not executed) ==")
        print("  The SUBJECT division's floor is the one that licenses calling a net a")
        print("  null, and it was measured there at 0 of 200 rows. This division is a")
        print("  control/exposure check, not a subject, and does not carry its own.")

    # ---- per arm against the base -------------------------------------------
    for a in [x for x in ("B", "C", "D") if x in ran]:
        gains = [r for r in rows if r["A"] not in DEC and r[a] in DEC]
        losses = [r for r in rows if r["A"] in DEC and r[a] not in DEC]
        flips = [r for r in rows if r["A"] in DEC and r[a] in DEC and r["A"] != r[a]]
        # THE CHANNEL A VERDICT COUNT MISSES.
        new_ab = [r for r in rows if r["A_rc"] != "134" and r[f"{a}_rc"] == "134"]
        fixed_ab = [r for r in rows if r["A_rc"] == "134" and r[f"{a}_rc"] != "134"]
        lo, hi = wilson(len(gains), len(rows))
        print(f"\n== arm {a} vs base A ==")
        print(
            f"  net={dec[a] - dec['A']:+d}   gains={len(gains)}  losses={len(losses)}  "
            f"flips={len(flips)}   gain rate 95% Wilson [{lo * 100:.2f}%, {hi * 100:.2f}%]"
        )
        print(
            f"  EXIT STATUS: aborts {ab['A']} -> {ab[a]}   "
            f"NEW aborts (clean in base, abort in arm) = {len(new_ab)}   "
            f"aborts CONVERTED to a clean exit = {len(fixed_ab)}"
        )
        if new_ab:
            print("  *** these are LOSSES the verdict column does not show: ***")
            for r in new_ab:
                print(f"      {r['A']:>7}(rc{r['A_rc']}) -> {r[a]:>7}(rc{r[f'{a}_rc']})  "
                      f"{os.path.basename(r['file'])[:56]}")
        for label, g in (("GAIN", gains), ("LOSS", losses), ("FLIP", flips)):
            for r in g[:12]:
                print(f"    {label} {r['A']:>7} -> {r[a]:>7}  status={r['status']:>7}  "
                      f"{os.path.basename(r['file'])[:52]}")
        if fixed_ab and not gains:
            print(
                f"  NOTE: {len(fixed_ab)} aborts became first-class declines and "
                f"NOT ONE was then decided. Converting the abort is necessary and "
                f"not sufficient."
            )

    # ---- soundness, with the comparable denominator printed beside the zero ---
    print("\n== soundness vs declared :status ==")
    for a in ran:
        comp = [r for r in rows if r[a] in DEC and r["status"] in DEC]
        dis = [r for r in comp if r[a] != r["status"]]
        print(f"  arm {a:>2}: comparable={len(comp):>4}  disagreements={len(dis)}")
        for r in dis:
            print(f"    *** DISAGREEMENT {r[a]} vs :status {r['status']}  {r['file']}")

    print("\n== first-arm balance (no arm may be systematically first) ==")
    print(f"  {dict(Counter(r['first'] for r in rows))}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
