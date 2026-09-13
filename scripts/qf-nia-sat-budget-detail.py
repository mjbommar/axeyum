#!/usr/bin/env python3
"""ADR-1950 in full: for the QF_NIA sat half, name WHICH budget refused, by how
much it was exceeded, and how much of the wall-clock budget was still unspent
when the process gave up.

The census split showed the sat half is dominated by the pre-lowering CNF clause
estimate. A previous lane already measured that RAISING that budget by the
estimator's own 9.4x slack decides 0 of 49, so the interesting quantity is not
the budget but the UNSPENT CLOCK behind the refusal: the estimate is
instantaneous, so whatever time the file had left is time no route used.
"""
import collections
import csv
import os
import re
import statistics
import subprocess

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                      capture_output=True, text=True,
                      cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
CENSUS = os.path.join(ROOT, "bench-results/qf-nia-sat-20260913/census-78-classified.tsv")
EST = re.compile(r"estimated (\d+) CNF clauses before lowering exceeds budget (\d+)")
BUDGET_MS = 24000


def main():
    rows = list(csv.DictReader(open(CENSUS), delimiter="\t"))
    print("=== the 3 files this tree DECIDES that the board calls unknown ===")
    for r in rows:
        if r["verdict"] in ("sat", "unsat"):
            print(f"  {r['verdict']:5s} {r['wall_s']:>6s}s truth={r['truth']:5s} "
                  f"decided_by={r['decided_by']:20s} {os.path.basename(r['file'])[:70]}")

    cnf = [r for r in rows if r["cause"] == "cnf-budget"]
    print(f"\n=== cnf-budget class: {len(cnf)} files "
          f"({sum(1 for r in cnf if r['truth'] == 'sat')} sat) ===")
    ratios, caps = [], collections.Counter()
    for r in cnf:
        m = EST.search(r["detail"])
        if m:
            est, cap = int(m.group(1)), int(m.group(2))
            ratios.append(est / cap)
            caps[cap] += 1
    print(f"budget that refused: {dict(caps)}")
    rs = sorted(ratios)
    print(f"estimate / budget  : min {rs[0]:.2f}x  med {statistics.median(rs):.2f}x  "
          f"max {rs[-1]:.2f}x   (n={len(rs)})")
    over = sum(1 for x in rs if x > 9.4)
    print(f"files whose estimate exceeds the budget by MORE than the 9.4x slack a "
          f"previous lane lifted: {over} of {len(rs)}")

    print("\n=== the unspent clock (ADR-1950: what was left of the 24 s) ===")
    for cause in ("cnf-budget", "ladder-clock"):
        grp = [r for r in rows if r["cause"] == cause and r["total_ms"] != "-1"]
        left = sorted(BUDGET_MS - int(r["total_ms"]) for r in grp)
        if not left:
            continue
        print(f"{cause:14s} n={len(left):3d}  unspent ms: min {left[0]} "
              f"med {statistics.median(left):.0f} max {left[-1]}")
        print(f"{'':14s}        unspent share of budget: "
              f"{100 * statistics.median(left) / BUDGET_MS:.0f}% (median)")

    print("\n=== polarity asymmetry: does the file use its clock? ===")
    for pole in ("sat", "unsat"):
        grp = [r for r in rows if r["truth"] == pole and r["total_ms"] != "-1"]
        used = [int(r["total_ms"]) / BUDGET_MS for r in grp]
        spent = sum(1 for u in used if u >= 0.98)
        print(f"  {pole:5s}: {spent:2d} of {len(grp):2d} files spend >=98% of the budget "
              f"({100 * spent / len(grp):.0f}%)   median used {100 * statistics.median(used):.0f}%")


if __name__ == "__main__":
    main()
