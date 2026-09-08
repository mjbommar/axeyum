#!/usr/bin/env python3
"""Per-file table for a warm-decider A/B run.

Totals hide the shape: on this population one file can carry most of the
filter's answers, so a total ratio and a median per-file ratio disagree. Both
are printed, and so is every file, because a summary that cannot be checked
against its own rows is a claim.
"""
import argparse
import collections
import json
import os
import statistics


def g(row, k):
    try:
        return int(row["counters"].get(k))
    except (TypeError, ValueError):
        return 0


ap = argparse.ArgumentParser()
ap.add_argument("--rows", required=True)
args = ap.parse_args()
rows = json.load(open(args.rows))

by_file = collections.defaultdict(dict)
arms = []
for r in rows:
    by_file[r["file"]][r["arm"]] = r
    if r["arm"] not in arms:
        arms.append(r["arm"])

hdr = f"{'file':44s}"
for a in arms:
    hdr += f" {a+'.off':>10s} {a+'.flt':>10s}"
print(hdr)
print("-" * len(hdr))

ratios_offline = []
ratios_total = []
for path, per in sorted(by_file.items()):
    if not all(a in per for a in arms):
        continue
    line = f"{os.path.basename(path)[:44]:44s}"
    for a in arms:
        line += f" {g(per[a],'theory_offline_checks'):10d} {g(per[a],'theory_filter_answers'):10d}"
    total = {a: g(per[a], "theory_offline_checks") + g(per[a], "theory_filter_answers") for a in arms}
    if total["off"] == 0:
        continue
    off_base = g(per["off"], "theory_offline_checks")
    if off_base > 0:
        ratios_offline.append(g(per["filter"], "theory_offline_checks") / off_base)
    ratios_total.append(total["filter"] / total["off"])
    line += f"  | warm-cache offline x{(g(per['filter'],'theory_offline_checks')/max(off_base,1)):5.2f}"
    print(line)

print()
print("columns: <arm>.off = theory_offline_checks, <arm>.flt = theory_filter_answers")
if ratios_offline:
    print(
        f"warm-vs-cold offline throughput (filter arm / off arm), per file: "
        f"median x{statistics.median(ratios_offline):.2f}, "
        f"min x{min(ratios_offline):.2f}, max x{max(ratios_offline):.2f}, "
        f"n={len(ratios_offline)}"
    )
    worse = [r for r in ratios_offline if r < 0.98]
    print(f"  files where warming made the offline path SLOWER (< x0.98): {len(worse)}")
if ratios_total:
    print(
        f"end-to-end live-set decisions (filter arm / off arm), per file: "
        f"median x{statistics.median(ratios_total):.2f}, n={len(ratios_total)}"
    )
