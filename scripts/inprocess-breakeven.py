"""Reproduce ADR-1750's break-even, in conflicts, from a fixed-conflict-budget sweep.

Break-even N solves:  T_pass + N / c_arm  ==  N / c_off
  =>  N = T_pass / (1/c_off - 1/c_arm)
and the wall-clock equivalent is N / c_off seconds of unreduced search.

Only files where BOTH arms exhausted the conflict budget are used: if one arm
decided early it analysed fewer conflicts, and its conflicts-per-second is then
a rate over a different (easier) part of the search. ADR-1750 applied the same
restriction and said so; dropping it inflates whichever arm decided.
"""

import json
import statistics
import sys

path = sys.argv[1] if len(sys.argv) > 1 else (
    "bench-results/inprocess-cost-2026-09-08/pass-conflicts-20k.jsonl"
)
rows = [json.loads(line) for line in open(path, encoding="utf-8") if line.strip()]
by_file = {}
for r in rows:
    by_file.setdefault(r["file"], {})[r["arm"]] = r

budget = None
for r in rows:
    if "max_conflicts" in r:
        budget = r["max_conflicts"]
        break
print(f"{len(rows)} rows, {len(by_file)} files, conflict budget {budget}\n")

print("| file | arm | verdict | conflicts | inproc s | search s | conf/s | props/conf |")
print("|---|---|---|---:|---:|---:|---:|---:|")
for f in sorted(by_file):
    for arm in ("off", "subsume", "bve", "preprocess"):
        r = by_file[f].get(arm)
        if r is None or "conflicts" not in r:
            print(f"| {f.split('/')[-1]} | {arm} | (no row / killed) | | | | | |")
            continue
        print(
            f"| {f.split('/')[-1]} | {arm} | {r['verdict']} | {r['conflicts']} | "
            f"{r['inprocess_seconds']:.3f} | {r['search_seconds']:.3f} | "
            f"{r['conflicts_per_second']:.0f} | {r['propagations_per_conflict']:.1f} |"
        )

print("\n## break-even (only files where BOTH arms exhausted the conflict budget)")
print("| file | arm | pass s | c_off | c_arm | break-even conflicts | = s of unreduced search |")
print("|---|---|---:|---:|---:|---:|---:|")
ratios = {a: [] for a in ("subsume", "bve", "preprocess")}
be_conf = {a: [] for a in ratios}
be_secs = {a: [] for a in ratios}
for f in sorted(by_file):
    off = by_file[f].get("off")
    if off is None or off.get("verdict") != "resource_out":
        continue
    c_off = off["conflicts_per_second"]
    for arm in ratios:
        r = by_file[f].get(arm)
        if r is None or r.get("verdict") != "resource_out":
            continue
        c_arm = r["conflicts_per_second"]
        ratios[arm].append(r["propagations_per_conflict"] / max(off["propagations_per_conflict"], 1e-9))
        if c_arm <= c_off:
            print(
                f"| {f.split('/')[-1]} | {arm} | {r['inprocess_seconds']:.3f} | {c_off:.0f} | "
                f"{c_arm:.0f} | NEVER (arm is slower per conflict too) | — |"
            )
            continue
        n = r["inprocess_seconds"] / (1.0 / c_off - 1.0 / c_arm)
        be_conf[arm].append(n)
        be_secs[arm].append(n / c_off)
        print(
            f"| {f.split('/')[-1]} | {arm} | {r['inprocess_seconds']:.3f} | {c_off:.0f} | "
            f"{c_arm:.0f} | {n:,.0f} | {n / c_off:.1f} |"
        )

print("\n## medians")
for arm in ratios:
    if be_conf[arm]:
        print(
            f"  {arm:12s} n={len(be_conf[arm]):2d}  median break-even "
            f"{statistics.median(be_conf[arm]):,.0f} conflicts = "
            f"{statistics.median(be_secs[arm]):.1f} s of unreduced search"
        )
    else:
        print(f"  {arm:12s} no file where both arms exhausted the budget AND the arm is faster")
    if ratios[arm]:
        print(
            f"  {arm:12s} median propagations/conflict vs off: "
            f"{statistics.median(ratios[arm]):.3f}  (n={len(ratios[arm])})"
        )
