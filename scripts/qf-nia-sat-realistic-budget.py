#!/usr/bin/env python3
"""ADR-1971 applied to the OUTPUT of the sizing surrogate, not just its input.

The surrogate handed every transformed file a fresh 24 s budget. A route added
to the dispatch does not get one: by the time an eager-split rung could run, the
census says `nia-linearize` has already spent ~6.7 s and the file is ~10.8 s in.
So the honest bracket is not "how many decide" but "how many decide WITHIN THE
BUDGET THE ROUTE WOULD ACTUALLY HAVE", and the two numbers differ.

Prints both, plus the budget each of the surrogate's winners would really get,
read per file from the census rather than from the class median.
"""
import csv
import os
import subprocess

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                      capture_output=True, text=True,
                      cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
D = os.path.join(ROOT, "bench-results/qf-nia-sat-20260913")
BUDGET_S = 24.0


def main():
    sur = {r["file"]: r for r in csv.DictReader(
        open(os.path.join(D, "eager-split-surrogate-29.tsv")), delimiter="\t")}
    cen = {r["file"]: r for r in csv.DictReader(
        open(os.path.join(D, "census-78-classified.tsv")), delimiter="\t")}

    print("=== the surrogate's winners, against the clock a real rung would get ===")
    print(f"{'decide_s':>8s} {'spent_before_s':>14s} {'left_s':>7s} {'fits?':>6s}  file")
    fits_tail = fits_first = 0
    rows = []
    for path, r in sur.items():
        if r["ours"] not in ("sat", "unsat"):
            continue
        c = cen[path]
        spent = int(c["total_ms"]) / 1000.0  # what the file burned before giving up
        left = BUDGET_S - spent
        ok = float(r["s"]) <= left
        fits_tail += ok
        fits_first += float(r["s"]) <= BUDGET_S
        rows.append((float(r["s"]), spent, left, ok, os.path.basename(path)))
    for s, spent, left, ok, base in sorted(rows):
        print(f"{s:8.1f} {spent:14.1f} {left:7.1f} {'yes' if ok else 'NO':>6s}  {base[:56]}")

    n = len(sur)
    print(f"\n=== the sizing bracket ===")
    print(f"  upper  (rung runs FIRST, whole 24 s budget): {fits_first} of {n}")
    print(f"  lower  (rung runs LAST, after the existing ladder spends its share): "
          f"{fits_tail} of {n}")
    print("\nThe upper bound is what the surrogate measured; it is only achievable by")
    print("moving the split AHEAD of the routes that currently consume the budget,")
    print("which taxes every other integer query. The lower bound is what appending")
    print("a rung buys. Both are reported because quoting either alone would be a")
    print("different decision.")


if __name__ == "__main__":
    main()
